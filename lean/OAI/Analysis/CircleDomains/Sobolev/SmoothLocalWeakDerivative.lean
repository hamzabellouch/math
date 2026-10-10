import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

namespace OAI

/-! A global distributional derivative agrees with the ordinary derivative
on any open set where its scalar has a smooth representative. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem integrable_mul_of_continuousOn_tsupport
    {U : Set ℂ} (hU : IsOpen U) {f φ : ℂ → ℝ}
    (hf : ContinuousOn f U) (hφ : Continuous φ) (hs : HasCompactSupport φ)
    (hsub : tsupport φ ⊆ U) : Integrable (fun z => f z * φ z) :=
  ((hf.mul hφ.continuousOn).continuous_of_tsupport_subset hU
    (tsupport_mul_subset_right.trans hsub)).integrable_of_hasCompactSupport hs.mul_left

 theorem integral_mul_fderiv_of_contDiffOn
    {U : Set ℂ} (hU : IsOpen U) {f φ : ℂ → ℝ}
    (hf : ContDiffOn ℝ 1 f U) (hφ : ContDiff ℝ 1 φ)
    (hs : HasCompactSupport φ) (hsub : tsupport φ ⊆ U) (v : ℂ) :
    (∫ z, f z * fderiv ℝ φ z v) = -(∫ z, fderiv ℝ f z v * φ z) := by
  have hdf : ContinuousOn (fun z => fderiv ℝ f z v) U :=
    (hf.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  have hdφ : Continuous (fun z => fderiv ℝ φ z v) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (integrable_mul_of_continuousOn_tsupport hU hdf hφ.continuous hs hsub)
    (integrable_mul_of_continuousOn_tsupport hU hf.continuousOn hdφ
      (hs.fderiv_apply (𝕜 := ℝ) v) ((tsupport_fderiv_apply_subset ℝ v).trans hsub))
    (integrable_mul_of_continuousOn_tsupport hU hf.continuousOn hφ.continuous hs hsub)
    (fun z hz => (hf.contDiffAt (hU.mem_nhds (hsub hz))).differentiableAt (by norm_num))
    (fun _ _ => hφ.differentiable (by norm_num) _)

 theorem weak_field_eq_smooth_derivative
    {U : Set ℂ} (hU : IsOpen U) {V f G : ℂ → ℝ} (v : ℂ)
    (hf : ContDiffOn ℝ 1 f U) (hG : MemLp G 2 volume)
    (heq : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ U → V z = f z)
    (hweak : ∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫ z, V z * fderiv ℝ φ z v) = -(∫ z, G z * φ z)) :
    ∀ᵐ z ∂(volume : Measure ℂ), z ∈ U → G z = fderiv ℝ f z v := by
  have hdf : ContinuousOn (fun z => fderiv ℝ f z v) U :=
    (hf.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  have hzero : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ U → G z - fderiv ℝ f z v = 0 := by
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (((hG.locallyIntegrable (by norm_num)).locallyIntegrableOn U).sub
        (hdf.locallyIntegrableOn hU.measurableSet))
    intro φ hφ hs hsub
    have hV : (∫ z, V z * fderiv ℝ φ z v) = ∫ z, f z * fderiv ℝ φ z v := by
      apply integral_congr_ae
      filter_upwards [heq] with z hz
      by_cases hzU : z ∈ U
      · rw [hz hzU]
      · have hnot : z ∉ tsupport (fun y => fderiv ℝ φ y v) :=
          fun h => hzU (hsub ((tsupport_fderiv_apply_subset ℝ v) h))
        have hd : fderiv ℝ φ z v = 0 := image_eq_zero_of_notMem_tsupport (f := fun y => fderiv ℝ φ y v) hnot
        simp only [hd, mul_zero]
    have hφ₁ : ContDiff ℝ 1 φ := hφ.of_le (by simp)
    have hi := integral_mul_fderiv_of_contDiffOn hU hf hφ₁ hs hsub v
    have hw := hweak φ hφ₁ hs
    rw [hV] at hw
    have he : (∫ z, G z * φ z) = ∫ z, fderiv ℝ f z v * φ z := by linarith
    have hiG : Integrable (fun z => φ z * G z) := by
      change Integrable (φ * G)
      exact (hφ.continuous.memLp_of_hasCompactSupport hs : MemLp φ 2 volume).integrable_mul hG
    have hid : Integrable (fun z => φ z * fderiv ℝ f z v) := by
      simpa only [mul_comm] using integrable_mul_of_continuousOn_tsupport hU hdf hφ.continuous hs hsub
    simp only [smul_eq_mul, Pi.sub_apply, mul_sub]
    rw [integral_sub hiG hid]
    simpa only [mul_comm, sub_eq_zero] using he
  filter_upwards [hzero] with z hz hzU
  exact sub_eq_zero.mp (hz hzU)

end CircleDomainRigidity

end

end OAI
