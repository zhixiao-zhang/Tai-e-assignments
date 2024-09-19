/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        CPFact cpfact = new CPFact();
        for (Var var: cfg.getIR().getParams()) {
            if (canHoldInt(var)) {
                cpfact.update(var, Value.getNAC());
            }
        }
        return cpfact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        for (Var v : fact.keySet()) {
            target.update(v, meetValue(fact.get(v), target.get(v)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isNAC() || v2.isNAC())
            return Value.getNAC();
        else if (v1.isUndef() || v2.isUndef())
            return v1.isUndef() ? v2 : v1;
        else if (v1.isConstant() && v2.isConstant())
            return (v1.getConstant() == v2.getConstant()) ? Value.makeConstant(v1.getConstant()) : Value.getNAC();
        else
            return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        CPFact outTmp = in.copy();
        if (stmt instanceof DefinitionStmt) { // inspect whether stmt is an assignment statement
            LValue val = stmt.getDef().isPresent() ? stmt.getDef().get() : null;
            if (val instanceof Var && canHoldInt((Var) val)) {
                outTmp.remove((Var) val);
                // calculate gen
                outTmp.update((Var) val, evaluate(((DefinitionStmt<?, ?>) stmt).getRValue(), in));
            }
        }
        return out.copyFrom(outTmp);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        if (exp instanceof Var)
            return in.get((Var) exp);
        if (exp instanceof IntLiteral)
            return Value.makeConstant(((IntLiteral) exp).getValue());
        if (exp instanceof BinaryExp binExp) {
            Value value1 = in.get(binExp.getOperand1());
            Value value2 = in.get(binExp.getOperand2());
            BinaryExp.Op op = binExp.getOperator();
            // if one of operands is NAC
            if (value1.isNAC() || value2.isNAC()) {
                if (!value2.isNAC() && binExp instanceof ArithmeticExp
                        && (op == ArithmeticExp.Op.DIV || op == ArithmeticExp.Op.REM)
                        && value2.getConstant() == 0) {
                    return Value.getUndef();
                }
                return Value.getNAC();
            }

            if (value1.isUndef() || value2.isUndef())
                return Value.getUndef();

            // if both operands are constant
            if (value1.isConstant() && value2.isConstant()) {
                // arithmetic expression
                if (binExp instanceof ArithmeticExp) {
                    // ZeroDivision case, return undef
                    if ((op == ArithmeticExp.Op.DIV || op == ArithmeticExp.Op.REM)
                            && value2.getConstant() == 0) {
                        return Value.getUndef();
                    }
                    return switch ((ArithmeticExp.Op) op) {
                        case ADD -> Value.makeConstant(value1.getConstant() + value2.getConstant());
                        case SUB -> Value.makeConstant(value1.getConstant() - value2.getConstant());
                        case MUL -> Value.makeConstant(value1.getConstant() * value2.getConstant());
                        case DIV -> Value.makeConstant(value1.getConstant() / value2.getConstant());
                        case REM -> Value.makeConstant(value1.getConstant() % value2.getConstant());
                    };
                } else if (binExp instanceof ConditionExp) {
                    return switch ((ConditionExp.Op) op) {
                        case EQ -> Value.makeConstant(value1.getConstant() == value2.getConstant() ? 1 : 0);
                        case NE -> Value.makeConstant(value1.getConstant() != value2.getConstant() ? 1 : 0);
                        case LT -> Value.makeConstant(value1.getConstant()  < value2.getConstant() ? 1 : 0);
                        case GT -> Value.makeConstant(value1.getConstant()  > value2.getConstant() ? 1 : 0);
                        case LE -> Value.makeConstant(value1.getConstant() <= value2.getConstant() ? 1 : 0);
                        case GE -> Value.makeConstant(value1.getConstant() >= value2.getConstant() ? 1 : 0);
                    };
                } else if (binExp instanceof ShiftExp) {
                    return switch ((ShiftExp.Op) op) {
                        case SHL -> Value.makeConstant(value1.getConstant() << value2.getConstant());
                        case SHR -> Value.makeConstant(value1.getConstant() >> value2.getConstant());
                        case USHR -> Value.makeConstant(value1.getConstant() >>> value2.getConstant());
                    };
                } else if (binExp instanceof BitwiseExp) {
                    return switch ((BitwiseExp.Op) op) {
                        case OR -> Value.makeConstant(value1.getConstant() | value2.getConstant());
                        case AND -> Value.makeConstant(value1.getConstant() & value2.getConstant());
                        case XOR -> Value.makeConstant(value1.getConstant() ^ value2.getConstant());
                    };
                } else {
                    return Value.getNAC();
                }
            }
        }
        return Value.getNAC();
    }
}
