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

package pascal.taie.analysis.dataflow.analysis;

import fj.P;
import pascal.taie.Assignment;
import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;
import polyglot.ast.Branch;
import polyglot.ast.Switch;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // Your task is to recognize dead code in ir and add it to deadCode
        // detect unreachable code

        ArrayDeque<Stmt> stmts = new ArrayDeque<>();
        Set<Stmt> reachable = new HashSet<>();
        Set<Stmt> reached = new HashSet<>();
        stmts.addLast(cfg.getEntry());
        reachable.add(cfg.getEntry());
        reachable.add(cfg.getExit());
        // Breadth-first search
        while (!stmts.isEmpty()) {
            Stmt s = stmts.pollFirst();
            reached.add(s);
            if (s instanceof AssignStmt<?,?> assignStmt) {
                SetFact<Var> liveVarsResult = liveVars.getResult(assignStmt);
                LValue lvalue = assignStmt.getLValue();
                RValue rvalue = assignStmt.getRValue();
                boolean f = true;
                if (lvalue instanceof Var) {
                    if (!liveVarsResult.contains((Var) lvalue)) {
                        if (hasNoSideEffect(rvalue)) {
                            f = false;
                        }
                    }
                }
                if (f)
                  reachable.add(assignStmt);
                for (Stmt succ : cfg.getSuccsOf(assignStmt)) {
                    if (!reached.contains(succ))
                        stmts.addLast(succ);
                }
            } else if (s instanceof If ifstmt) {
                Var operand1 = ifstmt.getCondition().getOperand1();
                Var operand2 = ifstmt.getCondition().getOperand2();
                Value val = ConstantPropagation.evaluate(ifstmt.getCondition(), constants.getInFact(ifstmt));
                reachable.add(s);
                if (val.isConstant()) {
                    if (val.getConstant() == 1) {
                        for (Edge<Stmt> edge : cfg.getOutEdgesOf(ifstmt)) {
                            Stmt target = edge.getTarget();
                            if (edge.getKind() == Edge.Kind.IF_TRUE && !reached.contains(target))
                                stmts.addLast(target);
                        }
                    } else if (val.getConstant() == 0) {
                        for (Edge<Stmt> edge : cfg.getOutEdgesOf(ifstmt)) {
                            Stmt target = edge.getTarget();
                            if (edge.getKind() == Edge.Kind.IF_FALSE && !reached.contains(target))
                                stmts.addLast(target);
                        }
                    }
                } else {
                    for (Stmt succ : cfg.getSuccsOf(ifstmt)) {
                        if (!reached.contains(succ))
                            stmts.addLast(succ);
                    }
                }
            } else if (s instanceof SwitchStmt switchStmt) {
                Var condition = switchStmt.getVar();
                CPFact result = constants.getInFact(switchStmt);
                reachable.add(switchStmt);
                if (result.get(condition).isConstant()) {
                    int index = result.get(condition).getConstant();
                    boolean matched = false;
                    for (Edge<Stmt> edge : cfg.getOutEdgesOf(switchStmt)) {
                        if (edge.getKind() == Edge.Kind.SWITCH_CASE &&
                                edge.getCaseValue() == index &&
                                !reached.contains(edge.getTarget())) {
                            matched = true;
                            stmts.addLast(edge.getTarget());
                        }
                    }
                    if (!matched && !reached.contains(switchStmt.getDefaultTarget())) {
                        stmts.addLast(switchStmt.getDefaultTarget());
                    }
                } else {
                    for (Stmt succ : cfg.getSuccsOf(switchStmt)) {
                        if (!reached.contains(succ)) {
                            stmts.addLast(succ);
                        }
                    }
                }
            } else {
                reachable.add(s);
                for (Stmt succ : cfg.getSuccsOf(s)) {
                    if (!reached.contains(succ)) {
                        stmts.addLast(succ);
                    }
                }
            }
        }
        for (Stmt s : ir.getStmts()) {
            if (!reachable.contains(s))
                deadCode.add(s);
        }
        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
