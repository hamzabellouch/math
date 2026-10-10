import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteDynkinDifference
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalizedWordBrackets
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialChartCoordinates

namespace OAI

/-! # A common translation bound for every word-chart scale -/

noncomputable section
namespace PolycyclicRecognition
open Module LieModule
open scoped BigOperators

variable {L J : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype J]

/-- The difference constant depends on the coefficient bound for the
bracket, so a bounded family of coordinate brackets shares one constant. -/
theorem exists_uniform_finiteDynkinPolynomial_difference_bound
    {c n : ℕ} (a : DynkinCoefficients c n) {C : ℝ} (hC : 0 ≤ C) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ b : Basis J ℝ L,
      (∀ i j k, |b.repr ⁅b i, b j⁆ k| ≤ C) →
      ∀ (X Y : Fin n → L) (M D : ℝ), 0 ≤ M → 0 ≤ D →
      (∀ i, ‖b.equivFun (X i)‖ ≤ M) → (∀ i, ‖b.equivFun (Y i)‖ ≤ M) →
      (∀ i, ‖b.equivFun (X i - Y i)‖ ≤ D) →
      ‖b.equivFun (finiteDynkinPolynomial a X - finiteDynkinPolynomial a Y)‖ ≤
        A * (1 + M) ^ c * D := by
  let K := (Fintype.card J : ℝ) ^ 2 * C
  have hK : 0 ≤ K := by positivity
  let A := ∑ d : Fin c, ∑ w : Fin (d.val + 1) → Fin n,
    |a d w| * (d.val + 1) * K ^ d.val
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro b hbracket X Y M D hM hD hX hY hXY
  have he : finiteDynkinPolynomial a X - finiteDynkinPolynomial a Y =
      ∑ d : Fin c, ∑ w : Fin (d.val + 1) → Fin n,
        a d w • (evalBracketWord X (rightNestedWord d.val w) -
          evalBracketWord Y (rightNestedWord d.val w)) := by
    simp only [finiteDynkinPolynomial, Finset.sum_sub_distrib, smul_sub]
  have hterm (d : Fin c) (w : Fin (d.val + 1) → Fin n) :
      ‖b.equivFun (a d w • (evalBracketWord X (rightNestedWord d.val w) -
        evalBracketWord Y (rightNestedWord d.val w)))‖ ≤
        (|a d w| * (d.val + 1) * K ^ d.val) * (1 + M) ^ c * D := by
    rw [map_smul, norm_smul, Real.norm_eq_abs]
    have hh := norm_basis_evalBracketWord_sub_le b X Y hC hM hD hbracket hX hY hXY
      (rightNestedWord d.val w)
    simp only [rightNestedWord_length, rightNestedWord_nodes, Nat.cast_add, Nat.cast_one] at hh
    have hp : M ^ d.val ≤ (1 + M) ^ c :=
      (pow_le_pow_left₀ hM (by linarith) _).trans
        (pow_le_pow_right₀ (by linarith) d.isLt.le)
    calc
      _ ≤ |a d w| * ((d.val + 1) * K ^ d.val * M ^ d.val * D) :=
        mul_le_mul_of_nonneg_left hh (abs_nonneg _)
      _ ≤ |a d w| * ((d.val + 1) * K ^ d.val * (1 + M) ^ c * D) := by gcongr
      _ = _ := by ring
  rw [he, map_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ d : Fin c, ∑ w : Fin (d.val + 1) → Fin n,
        (|a d w| * (d.val + 1) * K ^ d.val) * (1 + M) ^ c * D := by
      apply Finset.sum_le_sum
      intro d _
      rw [map_sum]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun w _ => hterm d w))
    _ = _ := by simp only [A, Finset.sum_mul]

end PolycyclicRecognition

end

end OAI
