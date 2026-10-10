import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.PolynomialFamilies

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {ι α : Type*} {L : ι → ℕ} {ea : α → Word} {a : ι → α}

lemma RunsPoly.ratOp (operation : KS.W13.ExpressionMachine.BinaryOp) {input : ι → ℚ × ℚ}
    (hinput : IsPoly L (fun index => (prodCode ratCode ratCode (input index)).length)) :
    RunsPoly L (ratOp operation) input := by
  refine ⟨hinput, ?_⟩
  apply (hinput.eval (5 * NaturalPolynomial.variable +
    6000000 * (NaturalPolynomial.variable + 1) ^ 3 + 6)).mono
  intro index
  have hlength := RoutineLength.output_length
    (KS.W13.ExpressionMachine.binaryArithmetic_spec operation (input index).1 (input index).2 [] []) 10
  have houtput : (ratCode (operation.eval (input index).1 (input index).2)).length ≤
      KS.W13.ExpressionMachine.binaryBudget (input index).1 (input index).2 := by
    simpa [KS.W13.ExpressionMachine.registers] using hlength
  have hpair : (ratCode (input index).1).length + (ratCode (input index).2).length ≤
      (prodCode ratCode ratCode (input index)).length := by
    rw [prodCode_length]
    omega
  have hpower := Nat.pow_le_pow_left (Nat.add_le_add_right hpair 1) 3
  have hleft := le_prodCode_left (ea := ratCode) (eb := ratCode) (input index)
  change ArithmeticRoutine.ticks operation (input index).1 (input index).2 ≤
    5 * (prodCode ratCode ratCode (input index)).length +
      6000000 * ((prodCode ratCode ratCode (input index)).length + 1) ^ 3 + 6
  simp only [ArithmeticRoutine.ticks, ArithmeticRoutine.encode,
    KS.W13.ExpressionMachine.binaryBudget, KS.W01.ratLength] at houtput ⊢
  simp only [ratCode] at *
  omega

variable {f g : α → ℚ} {r : Realizes ea ratCode f} {s : Realizes ea ratCode g}
lemma RunsPoly.add (hr : RunsPoly L r a) (hs : RunsPoly L s a) : RunsPoly L (r.add s) a :=
  (hr.both hs).then (RunsPoly.ratOp _ (hr.both hs).output)
lemma RunsPoly.sub (hr : RunsPoly L r a) (hs : RunsPoly L s a) : RunsPoly L (r.sub s) a :=
  (hr.both hs).then (RunsPoly.ratOp _ (hr.both hs).output)
lemma RunsPoly.mul (hr : RunsPoly L r a) (hs : RunsPoly L s a) : RunsPoly L (r.mul s) a :=
  (hr.both hs).then (RunsPoly.ratOp _ (hr.both hs).output)
lemma RunsPoly.div (hr : RunsPoly L r a) (hs : RunsPoly L s a) : RunsPoly L (r.div s) a :=
  (hr.both hs).then (RunsPoly.ratOp _ (hr.both hs).output)
end CurrentKS.Realization

end

end OAI
