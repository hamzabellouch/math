import OAI.Analysis.CircleDomains.Topology.RescaledPlaneBump
import OAI.Analysis.CircleDomains.Topology.SmallPerturbationHomeomorph

namespace OAI

/-! A local error with small differential gives an actual smooth ambient
perturbation, with exact values on the inner disk and compact support. -/
open Set Function Filter Metric
open scoped Topology ContDiff NNReal
noncomputable section
namespace CircleDomainRigidity

def localizedPlaneError (r : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ := planeScaledBump r z • f z

lemma localizedPlaneError_eventually_zero {r : ℝ} (hr : 0<r) (f : ℂ → ℂ)
    {z : ℂ} (hz : 2*r<‖z‖) : localizedPlaneError r f =ᶠ[𝓝 z] 0 := by
  filter_upwards [planeScaledBump_eventually_zero hr hz] with w hw
  simp only [localizedPlaneError,hw,zero_smul,Pi.zero_apply]

lemma localizedPlaneError_smooth {r : ℝ} (hr : 0<r) {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hsub : closedBall 0 (2*r)⊆U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiff ℝ ∞ (localizedPlaneError r f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z∈U
  · exact (planeScaledBump_smooth r).contDiffAt.smul ((hf z hz).contDiffAt (hU.mem_nhds hz))
  · have hn : 2*r<‖z‖ := lt_of_not_ge (fun h => hz (hsub (mem_closedBall_zero_iff.mpr h)))
    exact contDiffAt_const.congr_of_eventuallyEq (localizedPlaneError_eventually_zero hr f hn)

lemma localizedPlaneError_derivative_bound {r B d : ℝ}
    (hr : 0<r) (hB0 : 0≤B) (hd0 : 0≤d)
    (hB : ∀z,‖fderiv ℝ planeUnitBump z‖≤B)
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hsub : closedBall 0 (2*r)⊆U)
    (hf : ContDiffOn ℝ ∞ f U)
    (hf' : ∀z∈closedBall 0 (2*r),‖fderiv ℝ f z‖≤d)
    (hf0 : ∀z∈closedBall 0 (2*r),‖f z‖≤2*r*d) (z : ℂ) :
    ‖fderiv ℝ (localizedPlaneError r f) z‖≤d*(1+2*B) := by
  by_cases hz : z∈closedBall 0 (2*r)
  · have hfd := ((hf z (hsub hz)).contDiffAt (hU.mem_nhds (hsub hz))).differentiableAt (by simp)
    have hp := ((planeScaledBump_smooth r).differentiable (by simp) z).hasFDerivAt.smul hfd.hasFDerivAt
    change HasFDerivAt (localizedPlaneError r f) _ z at hp
    rw [hp.fderiv]
    calc
      ‖planeScaledBump r z • fderiv ℝ f z + (fderiv ℝ (planeScaledBump r) z).smulRight (f z)‖ ≤
          ‖planeScaledBump r z • fderiv ℝ f z‖+‖(fderiv ℝ (planeScaledBump r) z).smulRight (f z)‖ := norm_add_le _ _
      _ = |planeScaledBump r z| *‖fderiv ℝ f z‖ + ‖fderiv ℝ (planeScaledBump r) z‖*‖f z‖ := by
        rw [norm_smul,Real.norm_eq_abs,ContinuousLinearMap.norm_smulRight_apply]
      _ ≤ d+(B/r)*(2*r*d) := by
        have hu := planeScaledBump_unit r z
        apply add_le_add
        · rw [abs_of_nonneg hu.1]
          exact (mul_le_mul_of_nonneg_right hu.2 (norm_nonneg _)).trans (by simpa using hf' z hz)
        · exact mul_le_mul (planeScaledBump_derivative_bound hB hr z) (hf0 z hz)
            (norm_nonneg _) (div_nonneg hB0 hr.le)
      _ = d*(1+2*B) := by field_simp
  · have he := localizedPlaneError_eventually_zero hr f
      (lt_of_not_ge (fun h => hz (mem_closedBall_zero_iff.mpr h)))
    rw [he.fderiv_eq]
    rw [fderiv_zero]
    simp only [Pi.zero_apply,norm_zero]
    positivity

lemma exists_localized_smooth_perturbation {r B d : ℝ}
    (hr : 0<r) (hB0 : 0≤B) (hd0 : 0≤d) (hsmall : d*(1+2*B)<1)
    (hB : ∀z,‖fderiv ℝ planeUnitBump z‖≤B)
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hsub : closedBall 0 (2*r)⊆U)
    (hf : ContDiffOn ℝ ∞ f U)
    (hf' : ∀z∈closedBall 0 (2*r),‖fderiv ℝ f z‖≤d)
    (hf0 : ∀z∈closedBall 0 (2*r),‖f z‖≤2*r*d) :
    ∃H : ℂ ≃ₜ ℂ, ContDiff ℝ ∞ (H : ℂ → ℂ) ∧ ContDiff ℝ ∞ (H.symm : ℂ → ℂ) ∧
      (∀z∈closedBall 0 r,H z=z+f z) ∧ (∀z,2*r≤‖z‖ → H z=z) := by
  let L : ℝ≥0 := ⟨d*(1+2*B),by positivity⟩
  have hs := localizedPlaneError_smooth hr hU hsub hf
  have hl : LipschitzWith L (localizedPlaneError r f) :=
    lipschitzWith_of_nnnorm_fderiv_le (hs.differentiable (by simp))
      (fun z => localizedPlaneError_derivative_bound hr hB0 hd0 hB hU hsub hf hf' hf0 z)
  have hL : L<1 := hsmall
  refine ⟨smallPerturbationHomeomorph _ hl hL,smallPerturbationHomeomorph_smooth hl hL hs,
    smallPerturbationHomeomorph_inverse_smooth hl hL hs,?_,?_⟩
  · intro z hz
    simp only [smallPerturbationHomeomorph_apply,localizedPlaneError,
      planeScaledBump_one hr (mem_closedBall_zero_iff.mp hz),one_smul]
  · intro z hz
    simp only [smallPerturbationHomeomorph_apply,localizedPlaneError,
      planeScaledBump_zero hr hz,zero_smul,add_zero]

end CircleDomainRigidity

end

end OAI
