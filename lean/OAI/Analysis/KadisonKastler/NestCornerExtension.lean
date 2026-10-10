import OAI.Analysis.KadisonKastler.HilbertBlockCompletion
import OAI.Analysis.KadisonKastler.ProjectionNormDecomposition

namespace OAI

/-! # Extending a contractive corner across one nest projection -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem extend_contractive_nest_corner
    (P R Q T X : H →L[ℂ] H)
    (hP : IsStarProjection P) (hR : IsStarProjection R) (hQ : IsStarProjection Q)
    (hPR : P * R = P) (hX : ‖X‖ ≤ 1) (hXP : X * P = X)
    (hmatch : Q * X = Q * T * P) (hTR : ‖Q * T * R‖ ≤ 1) :
    ∃ Y : H →L[ℂ] H, ‖Y‖ ≤ 1 ∧ Y * P = X ∧ Y * R = Y ∧ Q * Y = Q * T * R := by
  let E := R - P
  let A := Q * X
  let B := Q * T * E
  let C := (1 - Q) * X
  have hRP := nested_projection_reverse hP hR hPR
  have hEP : E * P = 0 := by
    simp only [E, sub_mul, hRP, hP.isIdempotentElem.eq, sub_self]
  have hER : E * R = E := by
    simp only [E, sub_mul, hR.isIdempotentElem.eq, hPR]
  have hEE : E * E = E := by
    change E * (R - P) = E
    rw [mul_sub, hER, hEP, sub_zero]
  have hXR : X * R = X := by
    rw [← hXP, mul_assoc, hPR, hXP]
  have hAdjA : A.adjoint = P * star T * Q := by
    change star (Q * X) = _
    rw [hmatch, star_mul, star_mul, hP.isSelfAdjoint.star_eq, hQ.isSelfAdjoint.star_eq]
    simp only [mul_assoc]
  have hAdjB : B.adjoint = E * star T * Q := by
    change star (Q * T * E) = _
    simp only [E, star_mul, star_sub, hP.isSelfAdjoint.star_eq, hR.isSelfAdjoint.star_eq,
      hQ.isSelfAdjoint.star_eq, mul_assoc]
  have hrow : ∀ y, ‖A.adjoint y‖ ^ 2 + ‖B.adjoint y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    intro y
    rw [hAdjA, hAdjB]
    change ‖P ((star T * Q) y)‖ ^ 2 + ‖(R - P) ((star T * Q) y)‖ ^ 2 ≤ _
    rw [nested_projection_norm_sq_eq hP hPR]
    have hn : ‖R * star T * Q‖ ≤ 1 := by
      have hs : star (Q * T * R) = R * star T * Q := by
        simp only [star_mul, hQ.isSelfAdjoint.star_eq, hR.isSelfAdjoint.star_eq, mul_assoc]
      rw [← hs, norm_star]
      exact hTR
    have hb : ‖R ((star T * Q) y)‖ ≤ ‖y‖ := by
      simpa only [one_mul, mul_apply_eq_comp] using (R * star T * Q).le_of_opNorm_le hn y
    gcongr
  have hcol : ∀ x, ‖A x‖ ^ 2 + ‖C x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    intro x
    change ‖Q (X x)‖ ^ 2 + ‖(1 - Q) (X x)‖ ^ 2 ≤ _
    rw [projection_norm_sq_decomposition hQ]
    have hn : ‖X x‖ ≤ ‖x‖ := by simpa only [one_mul] using X.le_of_opNorm_le hX x
    gcongr
  obtain ⟨D, hD⟩ := exists_contractive_block_completion A B C hrow hcol
  let Y := X + B + (1 - Q) * D * E
  have hYP : Y * P = X := by
    simp only [Y, B, add_mul, mul_assoc, hXP, hEP, mul_zero, add_zero]
  have hYR : Y * R = Y := by
    simp only [Y, B, add_mul, mul_assoc, hXR, hER]
  have hQY : Q * Y = Q * T * R := by
    have hz : Q * (1 - Q) = 0 := by
      rw [mul_sub, mul_one, hQ.isIdempotentElem.eq, sub_self]
    simp only [Y, B, mul_add, ← mul_assoc, hQ.isIdempotentElem.eq, hz, zero_mul, add_zero]
    rw [hmatch]
    dsimp only [E]
    noncomm_ring
  refine ⟨Y, ?_, hYP, hYR, hQY⟩
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hAx : A (P x) = A x := by
    change (Q * X * P) x = (Q * X) x
    rw [mul_assoc, hXP]
  have hBx : B (E x) = B x := by
    change (Q * T * E * E) x = (Q * T * E) x
    rw [mul_assoc, hEE]
  have hCx : C (P x) = C x := by
    change ((1 - Q) * X * P) x = ((1 - Q) * X) x
    rw [mul_assoc, hXP]
  have hb := hD (P x) (E x)
  rw [hAx, hBx, hCx] at hb
  have hfirst : Q (Y x) = A x + B x := by
    have hqb : Q * B = B := by
      simp only [B, ← mul_assoc, hQ.isIdempotentElem.eq]
    have hz : Q * (1 - Q) = 0 := by
      rw [mul_sub, mul_one, hQ.isIdempotentElem.eq, sub_self]
    change (Q * Y) x = _
    simp only [Y, mul_add, ← mul_assoc, hz, zero_mul, add_zero, hqb, add_apply]
    rfl
  have hsecond : (1 - Q) (Y x) = (1 - Q) (C x + D (E x)) := by
    have hqb : (1 - Q) * B = 0 := by
      simp only [B, ← mul_assoc, sub_mul, one_mul, hQ.isIdempotentElem.eq, sub_self, zero_mul]
    change ((1 - Q) * Y) x = _
    simp only [Y, mul_add, ← mul_assoc, hqb, add_zero,
      hQ.one_sub.isIdempotentElem.eq, add_apply]
    have hc : (1 - Q) * C = C := by
      simp only [C, ← mul_assoc, hQ.one_sub.isIdempotentElem.eq]
    simp only [map_add]
    change C x + (1 - Q) (D (E x)) = ((1 - Q) * C) x + (1 - Q) (D (E x))
    rw [hc]
  calc
    ‖Y x‖ ^ 2 = ‖Q (Y x)‖ ^ 2 + ‖(1 - Q) (Y x)‖ ^ 2 :=
      (projection_norm_sq_decomposition hQ (Y x)).symm
    _ ≤ ‖A x + B x‖ ^ 2 + ‖C x + D (E x)‖ ^ 2 := by
      rw [hfirst, hsecond]
      gcongr
      exact projection_apply_norm_le hQ.one_sub _
    _ ≤ ‖P x‖ ^ 2 + ‖E x‖ ^ 2 := hb
    _ ≤ ‖x‖ ^ 2 := nested_projection_norm_sq hP hR hPR x

end

end KadisonKastler

end OAI
