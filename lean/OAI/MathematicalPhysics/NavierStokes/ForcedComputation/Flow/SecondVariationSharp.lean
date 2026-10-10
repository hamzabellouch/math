import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.VariationBounds

namespace OAI

/-! The time factor in the second-variation bound needed by the velocity
detector. This estimate applies in particular to the Euclidean plane. -/

namespace ForcedComputation
open Set

theorem exp_sub_one_le_mul_exp (r : ℝ) :
    Real.exp r - 1 ≤ r * Real.exp r := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-r)) (Real.exp_pos r).le
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  nlinarith

theorem second_variation_bound_sharp_mul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B B' : ℝ → E} {K C t : ℝ}
    (hK : 0 < K) (hC : 0 ≤ C) (ht : 0 ≤ t) (hc : ContinuousOn B (Icc 0 t))
    (hd : ∀ s ∈ Ico 0 t, HasDerivAt B (B' s) s) (h₀ : B 0 = 0)
    (hb : ∀ s ∈ Ico 0 t,
      ‖B' s‖ ≤ K * ‖B s‖ + C * K * Real.exp (2 * K * s)) :
    ‖B t‖ ≤ C * K * t * Real.exp (3 * K * t) := by
  have hbound (s : ℝ) (hs : s ∈ Ico 0 t) :
      ‖B' s‖ ≤ K * ‖B s‖ + C * K * Real.exp (2 * K * t) := by
    apply (hb s hs).trans
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hK.le)
    apply Real.exp_le_exp.mpr
    nlinarith [hs.2.le]
  have h := norm_le_gronwallBound_of_norm_deriv_right_le
    (K := K) (ε := C * K * Real.exp (2 * K * t)) hc
    (fun s hs => (hd s hs).hasDerivWithinAt)
    (show ‖B 0‖ ≤ 0 by simp [h₀]) hbound t ⟨ht, le_rfl⟩
  rw [gronwallBound_of_K_ne_0 hK.ne'] at h
  simp only [sub_zero, zero_mul, zero_add] at h
  have hcancel : (C * K * Real.exp (2 * K * t)) / K = C * Real.exp (2 * K * t) := by
    field_simp [hK.ne']
  rw [hcancel] at h
  calc
    ‖B t‖ ≤ C * Real.exp (2 * K * t) * (Real.exp (K * t) - 1) := h
    _ ≤ C * Real.exp (2 * K * t) * (K * t * Real.exp (K * t)) :=
      mul_le_mul_of_nonneg_left (exp_sub_one_le_mul_exp _)
        (mul_nonneg hC (Real.exp_pos _).le)
    _ = C * K * t * (Real.exp (2 * K * t) * Real.exp (K * t)) := by ring
    _ = C * K * t * Real.exp (3 * K * t) := by
      rw [← Real.exp_add]
      congr 2
      ring

end ForcedComputation

end OAI
