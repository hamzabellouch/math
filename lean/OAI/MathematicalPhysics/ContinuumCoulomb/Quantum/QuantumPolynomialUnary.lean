import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCircuitCode

namespace OAI

/-! A fixed natural polynomial has a literal unary evaluation program. The
polynomial is compiled by Horner recursion, using unary addition and multiplication. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPolynomialUnary
open ExactQuantumFactoring.BitStackProgram

noncomputable def program (p : Polynomial ℕ) :
    Procedure unaryCode unaryCode p.eval := by
  refine Polynomial.recOnHorner p ?_ ?_ ?_
  · exact (Procedure.constant unaryCode unaryCode 0).congrFun (by intro n; simp)
  · intro q a _ _ hq
    exact (Procedure.unaryAdd.comp
      (hq.pair (Procedure.constant unaryCode unaryCode a))).congrFun (by
        intro n
        simp only [Function.comp_apply,Polynomial.eval_add,Polynomial.eval_C])
  · intro q _ hq
    exact (Procedure.unaryMul.comp (hq.pair (Procedure.identity unaryCode))).congrFun (by
      intro n
      simp only [Function.comp_apply,id_eq,Polynomial.eval_mul,Polynomial.eval_X])

end ContinuumCoulomb.QuantumPolynomialUnary

end

end OAI
