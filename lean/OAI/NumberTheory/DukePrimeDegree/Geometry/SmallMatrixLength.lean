import OAI.NumberTheory.DukePrimeDegree.Geometry.ConjugationRadius

namespace OAI

/-! # Quantitative logarithmic length near the identity

The algebraic inverse identity bounds the inverse norm by two on a
half-unit operator ball. Consequently logarithmic length is bounded by
three times the displacement norm there.
-/

noncomputable section
open Matrix
open scoped Matrix.Norms.Operator
namespace DukePrimeDegree
open PrimeDegreePackets

lemma specialLinear_inverse_norm_le_two {n : ℕ} (hn : 0 < n)
    (g : G n) (hg : ‖g.val-1‖ ≤ 1/2) : ‖(g⁻¹).val‖ ≤ 2 := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have he : (g⁻¹).val = 1-(g⁻¹).val*(g.val-1) := by
    rw [Matrix.mul_sub,Matrix.mul_one]
    have hmul : (g⁻¹).val*g.val = (1 : Matrix (Fin n) (Fin n) ℝ) := by
      change (g⁻¹*g).val=1
      simp
    rw [hmul]
    abel
  have hbound : ‖(g⁻¹).val‖ ≤ 1+‖(g⁻¹).val‖*‖g.val-1‖ := by
    calc
      _ = ‖1-(g⁻¹).val*(g.val-1)‖ := congrArg norm he
      _ ≤ ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖+‖(g⁻¹).val*(g.val-1)‖ := norm_sub_le _ _
      _ ≤ _ := by
        rw [norm_one]
        exact add_le_add le_rfl (norm_mul_le (g⁻¹).val (g.val-1))
  nlinarith [mul_le_mul_of_nonneg_left hg (norm_nonneg (g⁻¹).val)]

lemma matrixLogLength_le_three_norm {n : ℕ} (hn : 0 < n)
    (g : G n) (hg : ‖g.val-1‖ ≤ 1/2) :
    matrixLogLength g ≤ 3*‖g.val-1‖ := by
  have hi := specialLinear_inverse_norm_le_two hn g hg
  have he : (g⁻¹).val-1 = -((g⁻¹).val*(g.val-1)) := by
    rw [Matrix.mul_sub,Matrix.mul_one]
    have hmul : (g⁻¹).val*g.val = (1 : Matrix (Fin n) (Fin n) ℝ) := by
      change (g⁻¹*g).val=1
      simp
    rw [hmul]
    abel
  have hdiff : ‖(g⁻¹).val-1‖ ≤ 2*‖g.val-1‖ := by
    rw [he,norm_neg]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hi (norm_nonneg _))
  have H := matrixLogLength_le_displacements g
  linarith

lemma matrixLogLength_le_three_card_radius {n : ℕ} (hn : 0 < n)
    {r : ℝ} (hr : 0 ≤ r) (hsmall : (n:ℝ)*r ≤ 1/2)
    {g : G n} (hg : g ∈ matrixBall n r) :
    matrixLogLength g ≤ 3*(n:ℝ)*r := by
  have hnorm := matrix_operator_norm_le_card_mul (g.val-1) hr (fun i j => (hg i j).le)
  exact (matrixLogLength_le_three_norm hn g (hnorm.trans hsmall)).trans (by nlinarith)

end DukePrimeDegree

end

end OAI
