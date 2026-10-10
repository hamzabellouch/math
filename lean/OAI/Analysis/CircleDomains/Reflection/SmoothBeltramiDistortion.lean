import OAI.Geometry.Cannon.Beltrami.TwoPointNormalize

namespace OAI

/-! The actual smooth principal maps and their inverses satisfy the same
uniform quasiconformal distortion bound. -/
open MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open CannonBeltrami

lemma smooth_homeomorph_partialZ_ne_zero (F : ℂ ≃ₜ ℂ)
    (hF : Differentiable ℝ (F : ℂ → ℂ))
    (hFi : Differentiable ℝ (F.symm : ℂ → ℂ)) (μ : ℂ → ℂ)
    (he : ∀ z, partialBar F z=μ z*partialZ F z) (z : ℂ) : partialZ F z ≠ 0 := by
  intro hz
  have hz' : partialBar F z=0 := by rw [he z, hz, mul_zero]
  have hzero : fderiv ℝ (F : ℂ → ℂ) z 1=0 := by
    rw [fderiv_wirtinger F z, hz, hz']
    simp
  have hc := ((hFi (F z)).hasFDerivAt.comp z (hF z).hasFDerivAt).fderiv
  have hid : (F.symm : ℂ → ℂ) ∘ F=id := funext F.symm_apply_apply
  rw [hid, fderiv_id] at hc
  have hh := congrArg (fun L : ℂ →L[ℝ] ℂ => L 1) hc
  simp only [ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
    hzero, map_zero] at hh
  exact one_ne_zero hh

lemma smooth_beltrami_two_sided_distortion (F : ℂ ≃ₜ ℂ)
    (hF : ContDiff ℝ ∞ (F : ℂ → ℂ))
    (hFi : ContDiff ℝ ∞ (F.symm : ℂ → ℂ)) (μ : ℂ → ℂ)
    {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1) (hb : ∀ z, ‖μ z‖ ≤ k)
    (he : ∀ z, partialBar F z=μ z*partialZ F z) :
    (∀ z, ‖fderiv ℝ (F : ℂ → ℂ) z‖^2 ≤
      ((1+k)/(1-k))*|(fderiv ℝ (F : ℂ → ℂ) z).det|) ∧
    ∀ z, ‖fderiv ℝ (F.symm : ℂ → ℂ) z‖^2 ≤
      ((1+k)/(1-k))*|(fderiv ℝ (F.symm : ℂ → ℂ) z).det| := by
  have hd := hF.differentiable (by simp)
  have hdi := hFi.differentiable (by simp)
  have hn := smooth_homeomorph_partialZ_ne_zero F hd hdi μ he
  constructor
  · intro z
    exact (wirtinger_energy_distortion _ _ _ (fderiv_wirtinger F z) hk hk1 (by
      rw [he, norm_mul]
      exact mul_le_mul_of_nonneg_right (hb z) (norm_nonneg _))).2
  · intro z
    have hi := inverse_partialBar F hd hdi μ he hn z
    exact (wirtinger_energy_distortion _ _ _ (fderiv_wirtinger F.symm z) hk hk1 (by
      rw [hi, norm_mul, norm_neg, norm_star]
      exact mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _))).2

end CircleDomainRigidity

end

end OAI
