import OAI.Analysis.BernoulliCone.HarmonicRadial

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff BigOperators
namespace Bernoulli.HarmonicKernel
variable {d : ℕ}

def profile (t : ℝ) : ℝ := expNegInvGlue (1-t)
def kernelProfile (t : ℝ) : ℝ := -2 * deriv profile t
def potential (x : Space d) : ℝ := profile (‖x‖^2)
def rawKernel (x : Space d) : ℝ := kernelProfile (‖x‖^2)

lemma contDiff_profile : ContDiff ℝ ∞ profile :=
  expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id)

lemma deriv_profile (t : ℝ) : deriv profile t = -((1-t)⁻¹)^2 * profile t := by
  have hh := (expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : Polynomial ℝ) (1-t)).comp t
    ((hasDerivAt_id t).const_sub 1)
  have hh' : HasDerivAt profile (-((1-t)⁻¹)^2 * profile t) t := by
    convert! hh using 1
    · funext s
      simp [profile]
    · simp [profile]
  exact hh'.deriv

lemma kernelProfile_eq (t : ℝ) :
    kernelProfile t = 2 * ((1-t)⁻¹)^2 * profile t := by
  rw [kernelProfile,deriv_profile]
  ring

lemma contDiff_kernelProfile : ContDiff ℝ ∞ kernelProfile :=
  contDiff_const.mul (contDiff_infty_iff_deriv.mp contDiff_profile).2

lemma profile_zero {t : ℝ} (ht : 1 ≤ t) : profile t = 0 :=
  expNegInvGlue.zero_of_nonpos (sub_nonpos.mpr ht)

lemma kernelProfile_zero {t : ℝ} (ht : 1 ≤ t) : kernelProfile t = 0 := by
  rw [kernelProfile_eq,profile_zero ht,mul_zero]

lemma kernelProfile_nonneg (t : ℝ) : 0 ≤ kernelProfile t := by
  rw [kernelProfile_eq]
  exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (expNegInvGlue.nonneg _)

lemma kernelProfile_pos {t : ℝ} (ht : t < 1) : 0 < kernelProfile t := by
  rw [kernelProfile_eq]
  exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos (inv_pos.mpr (sub_pos.mpr ht))))
    (expNegInvGlue.pos_of_pos (sub_pos.mpr ht))

lemma contDiff_rawKernel : ContDiff ℝ ∞ (rawKernel : Space d → ℝ) :=
  contDiff_kernelProfile.comp (contDiff_id.norm_sq ℝ)

lemma contDiff_potential : ContDiff ℝ ∞ (potential : Space d → ℝ) :=
  contDiff_profile.comp (contDiff_id.norm_sq ℝ)

lemma rawKernel_zero {x : Space d} (hx : x ∉ Metric.closedBall 0 1) : rawKernel x = 0 := by
  apply kernelProfile_zero
  have hh : 1 < ‖x‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hx
  nlinarith

lemma rawKernel_compact : HasCompactSupport (rawKernel : Space d → ℝ) :=
  HasCompactSupport.intro (isCompact_closedBall 0 1) (fun _ hx => rawKernel_zero hx)

lemma rawKernel_nonneg (x : Space d) : 0 ≤ rawKernel x := kernelProfile_nonneg _

lemma rawKernel_mass_pos : 0 < ∫ x : Space d, rawKernel x := by
  apply contDiff_rawKernel.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    rawKernel_compact rawKernel_nonneg
  exact (kernelProfile_pos (by simp : ‖(0 : Space d)‖^2 < 1)).ne'

/-- Compact radial potential centered at `a` with positive radius `r`.
Its scale derivative produces an averaging kernel by the radial Laplacian. -/
def scaledPotential (r : ℝ) (a x : Space d) : ℝ := profile (‖x-a‖^2 / r^2)

lemma contDiff_scaledPotential (r : ℝ) (a : Space d) :
    ContDiff ℝ ∞ (scaledPotential r a) :=
  contDiff_profile.comp (((contDiff_id.sub contDiff_const).norm_sq ℝ).div_const (r^2))

lemma scaledPotential_zero {r : ℝ} (hr : 0 < r) (a : Space d) {x : Space d}
    (hx : x ∉ Metric.closedBall a r) : scaledPotential r a x = 0 := by
  apply profile_zero
  have hh : r < ‖x-a‖ := by simpa only [Metric.mem_closedBall,dist_eq_norm,not_le] using hx
  apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
  nlinarith

lemma scaledPotential_support {r : ℝ} (hr : 0 < r) (a : Space d) :
    tsupport (scaledPotential r a) ⊆ Metric.closedBall a r := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra hh
  exact hx (scaledPotential_zero hr a hh)

lemma scaledPotential_test {D : Set (Space d)} {r : ℝ} (hr : 0 < r) (a : Space d)
    (hB : Metric.closedBall a r ⊆ D) : Test D (scaledPotential r a) := by
  exact ⟨contDiff_scaledPotential r a,
    HasCompactSupport.intro (isCompact_closedBall a r) (fun _ hx => scaledPotential_zero hr a hx),
    (scaledPotential_support hr a).trans hB⟩
end Bernoulli.HarmonicKernel

end
end

end OAI
