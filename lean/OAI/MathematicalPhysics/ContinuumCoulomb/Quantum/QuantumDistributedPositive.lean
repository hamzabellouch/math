import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumReferenceLower
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumDistributedFamily

namespace OAI

/-! Every concrete distributed-history term is positive semidefinite. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaDiagonalBranch_nonnegative {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → Prop) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (u : α → ℂ) :
    0 ≤ qmaQuadratic (Matrix.diagonal (fun s => if p s then (a:ℂ) else (b:ℂ))) u := by
  have he : (fun s => if p s then (a:ℂ) else (b:ℂ)) =
      (fun s => ((if p s then a else b : ℝ):ℂ)) := by
    funext s
    split_ifs <;> rfl
  rw [he,qmaQuadratic_diagonal_real]
  apply Finset.sum_nonneg
  intro s _
  apply mul_nonneg _ (Complex.normSq_nonneg _)
  split_ifs <;> assumption

theorem qmaDistributedTerm_nonnegative (c : QMACircuit)
    (τ : Fin (c.work+1) → Fin (c.gates.length+1)) (t : QMACircuitTerm c)
    (u : (QMACircuitQubit c → Fin 2) → ℂ) :
    0 ≤ qmaQuadratic (qmaDistributedTermMatrix c τ t) u := by
  rcases t with i | (b | (i | (v | t)))
  · change 0 ≤ qmaQuadratic (qmaClockFaultTerm c i) u
    unfold qmaClockFaultTerm qmaPairDiagonal
    simp only [qmaQuadratic,Matrix.mulVec_diagonal,dotProduct,Pi.star_apply,Complex.re_sum]
    apply Finset.sum_nonneg
    intro s _
    split_ifs <;> simp [Complex.mul_re]
    all_goals nlinarith [sq_nonneg (u s).re,sq_nonneg (u s).im]
  · fin_cases b
    · change 0 ≤ qmaQuadratic (qmaClockLeftTerm c) u
      unfold qmaClockLeftTerm qmaBitDiagonal
      simp only [qmaQuadratic,Matrix.mulVec_diagonal,dotProduct,Pi.star_apply,Complex.re_sum]
      apply Finset.sum_nonneg
      intro s _
      split_ifs <;> simp [Complex.mul_re]
      all_goals nlinarith [sq_nonneg (u s).re,sq_nonneg (u s).im]
    · change 0 ≤ qmaQuadratic (qmaClockRightTerm c) u
      unfold qmaClockRightTerm qmaBitDiagonal
      simp only [qmaQuadratic,Matrix.mulVec_diagonal,dotProduct,Pi.star_apply,Complex.re_sum]
      apply Finset.sum_nonneg
      intro s _
      split_ifs <;> simp [Complex.mul_re]
      all_goals nlinarith [sq_nonneg (u s).re,sq_nonneg (u s).im]
  · change 0 ≤ qmaQuadratic (qmaDistributedInputTerm c τ i) u
    unfold qmaDistributedInputTerm
    simp only [qmaQuadratic,Matrix.mulVec_diagonal,dotProduct,Pi.star_apply,Complex.re_sum]
    apply Finset.sum_nonneg
    intro s _
    split_ifs <;> simp [Complex.mul_re]
    all_goals nlinarith [sq_nonneg (u s).re,sq_nonneg (u s).im]
  · change 0 ≤ qmaQuadratic (qmaOutputTerm c) u
    unfold qmaOutputTerm qmaPairDiagonal
    simp only [qmaQuadratic,Matrix.mulVec_diagonal,dotProduct,Pi.star_apply,Complex.re_sum]
    apply Finset.sum_nonneg
    intro s _
    split_ifs <;> simp [Complex.mul_re]
    all_goals nlinarith [sq_nonneg (u s).re,sq_nonneg (u s).im]
  · change 0 ≤ qmaQuadratic (((14*(c.work+1)+8)*c.gates.length:ℂ) •
      ((qmaLocalPropagationDelta c t).conjTranspose*qmaLocalPropagationDelta c t)) u
    have he : ((14*(c.work+1)+8)*c.gates.length:ℂ) =
        (((14*(c.work+1)+8)*c.gates.length:ℝ):ℂ) := by push_cast; rfl
    rw [he,qmaQuadratic_smul,qmaQuadratic_gram]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _))

end ContinuumCoulomb

end

end OAI
