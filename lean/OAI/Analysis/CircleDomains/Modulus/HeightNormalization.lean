import OAI.Analysis.CircleDomains.Sobolev.VerticalWeakConstant

namespace OAI

/-! Exterior decay removes the additive constant in a zero-error height. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem normalized_vertical_weak_gradient
    {v : ℂ → ℝ} (hv : Continuous v)
    (hw : DeGiorgi.HasWeakGrad (heightLimitGradient 0 0) (v ∘ complexPlaneCoordinates) univ)
    {R A : ℝ} (hdecay : ∀ z : ℂ, R ≤ ‖z‖ → |v z-z.im| ≤ A/‖z‖) :
    v = Complex.im := by
  obtain ⟨c, hc⟩ := vertical_translation_of_weak_gradient
    (hv.comp complexPlaneCoordinates.continuous) hw
  have hcz (z : ℂ) : v z = z.im+c := by
    have h := hc (complexPlaneCoordinates.symm z)
    have hy : (complexPlaneCoordinates.symm z) 1 = z.im :=
      congrArg Complex.im (complexPlaneCoordinates.apply_symm_apply z)
    simpa only [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply, hy] using h
  have hc0 : c = 0 := by
    by_contra hn
    have hcp : 0 < |c| := abs_pos.mpr hn
    let T := max R ((|A|+1)/|c|)
    have hT : 0 < T := lt_of_lt_of_le (div_pos (by positivity) hcp) (le_max_right _ _)
    have hnorm : ‖(⟨T, 0⟩ : ℂ)‖ = T := by
      change ‖(T : ℂ)‖ = T
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
    have h := hdecay (⟨T, 0⟩ : ℂ) (by rw [hnorm]; exact le_max_left _ _)
    rw [hcz, add_sub_cancel_left, hnorm] at h
    have hm : |c| * T ≤ A := (le_div_iff₀ hT).mp h
    have ht : |A|+1 ≤ |c| * T := by
      have ht := mul_le_mul_of_nonneg_left (le_max_right R ((|A|+1)/|c|)) hcp.le
      rwa [mul_div_cancel₀ _ hcp.ne'] at ht
    linarith [le_abs_self A]
  funext z
  simpa only [hc0, add_zero] using hcz z

end CircleDomainRigidity

end

end OAI
