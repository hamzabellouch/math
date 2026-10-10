import Mathlib.Analysis.ODE.Gronwall

namespace OAI

/-! The quantitative inequalities needed for the first two variational
equations of the planar processor. Doubling the computed coefficient bound
puts both estimates in the form used in the manuscript. -/

namespace ForcedComputation
open Set

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem first_variation_bound_mul {J J' : ℝ → E} {K C t : ℝ} (ht : 0 ≤ t)
    (hc : ContinuousOn J (Icc 0 t))
    (hd : ∀ s ∈ Ico 0 t, HasDerivAt J (J' s) s)
    (h₀ : ‖J 0‖ ≤ C) (hb : ∀ s ∈ Ico 0 t, ‖J' s‖ ≤ K * ‖J s‖) :
    ‖J t‖ ≤ C * Real.exp (K * t) := by
  have h := norm_le_gronwallBound_of_norm_deriv_right_le (K := K) (ε := 0) hc
    (fun s hs => (hd s hs).hasDerivWithinAt) h₀
    (fun s hs => by simpa only [add_zero] using hb s hs) t ⟨ht, le_rfl⟩
  simpa only [gronwallBound_ε0, sub_zero] using h

theorem first_variation_bound {J J' : ℝ → E} {K t : ℝ} (ht : 0 ≤ t)
    (hc : ContinuousOn J (Icc 0 t))
    (hd : ∀ s ∈ Ico 0 t, HasDerivAt J (J' s) s)
    (h₀ : ‖J 0‖ ≤ 1) (hb : ∀ s ∈ Ico 0 t, ‖J' s‖ ≤ K * ‖J s‖) :
    ‖J t‖ ≤ Real.exp (K * t) := by
  simpa only [one_mul] using first_variation_bound_mul ht hc hd h₀ hb

theorem second_variation_bound_mul {B B' : ℝ → E} {K C t : ℝ}
    (hK : 0 < K) (hC : 0 ≤ C) (ht : 0 ≤ t) (hc : ContinuousOn B (Icc 0 t))
    (hd : ∀ s ∈ Ico 0 t, HasDerivAt B (B' s) s)
    (h₀ : B 0 = 0)
    (hb : ∀ s ∈ Ico 0 t,
      ‖B' s‖ ≤ K * ‖B s‖ + C * K * Real.exp (2 * K * s)) :
    ‖B t‖ ≤ C * (Real.exp (4 * K * t) - Real.exp (2 * K * t)) := by
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
  dsimp only at h
  simp only [sub_zero, zero_mul, zero_add] at h
  have hcancel : (C * K * Real.exp (2 * K * t)) / K = C * Real.exp (2 * K * t) := by
    field_simp [hK.ne']
  rw [hcancel] at h
  have heq : Real.exp (2 * K * t) * (Real.exp (K * t) - 1) =
      Real.exp (3 * K * t) - Real.exp (2 * K * t) := by
    have he : 2 * K * t + K * t = 3 * K * t := by ring
    rw [mul_sub, ← Real.exp_add, mul_one, he]
  rw [mul_assoc, heq] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply sub_le_sub_right
  apply Real.exp_le_exp.mpr
  nlinarith

theorem second_variation_bound {B B' : ℝ → E} {K t : ℝ}
    (hK : 0 < K) (ht : 0 ≤ t) (hc : ContinuousOn B (Icc 0 t))
    (hd : ∀ s ∈ Ico 0 t, HasDerivAt B (B' s) s)
    (h₀ : B 0 = 0)
    (hb : ∀ s ∈ Ico 0 t,
      ‖B' s‖ ≤ K * ‖B s‖ + K * Real.exp (2 * K * s)) :
    ‖B t‖ ≤ Real.exp (4 * K * t) - Real.exp (2 * K * t) := by
  simpa only [one_mul] using second_variation_bound_mul (C := 1) hK
    (by norm_num) ht hc hd h₀ (by simpa only [one_mul] using hb)

end
end ForcedComputation

end OAI
