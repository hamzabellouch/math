import OAI.Probability.ContinuumTransition.SupportGenerators

namespace OAI

section

open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set

namespace ContinuumTemperature

noncomputable section
open scoped ContDiff

def shellDelta : ℝ := 1 / 1000

def coreProfile (t r : ℝ) : ℝ :=
  if r < Real.exp (-t) then t ^ 2 + (Real.exp (-t) / r) ^ 12
  else if r ≤ (1 + shellDelta) * Real.exp (-t) then 0
  else if r < 1 then t ^ 2 else 0

noncomputable def baseKernel (x : Space) : ℝ := Real.smoothTransition (2 - 2 * ‖x‖)

theorem baseKernel_nonneg (x : Space) : 0 ≤ baseKernel x := Real.smoothTransition.nonneg _

theorem baseKernel_eq_one {x : Space} (hx : ‖x‖ ≤ 1 / 2) : baseKernel x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  linarith

theorem baseKernel_eq_zero {x : Space} (hx : 1 ≤ ‖x‖) : baseKernel x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  linarith

theorem contDiff_baseKernel : ContDiff ℝ ∞ baseKernel := by
  have heq : baseKernel = fun x : Space =>
      (ContDiffBumpBase.ofInnerProductSpace Space).toFun 2 ((2 : ℝ) • x) := by
    funext x
    norm_num [baseKernel, ContDiffBumpBase.ofInnerProductSpace, norm_smul]
  rw [heq]
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hmem : ((2 : ℝ), (2 : ℝ) • x) ∈ Ioi (1 : ℝ) ×ˢ (Set.univ : Set Space) := by
    norm_num
  have hdiff := (ContDiffBumpBase.ofInnerProductSpace Space).smooth.contDiffAt
    ((isOpen_Ioi.prod isOpen_univ).mem_nhds hmem)
  have hcomp := hdiff.comp x (contDiffAt_const.prodMk
    (ContDiffAt.const_smul (2 : ℝ) contDiffAt_id) :
      ContDiffAt ℝ ∞ (fun y : Space => ((2 : ℝ), (2 : ℝ) • y)) x)
  exact hcomp

theorem hasCompactSupport_baseKernel : HasCompactSupport baseKernel := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Space) 1)
  intro x hx
  exact baseKernel_eq_zero (by simpa using (not_lt.mp (fun h => hx (by simpa using h.le))))

theorem integrable_baseKernel : Integrable baseKernel :=
  contDiff_baseKernel.continuous.integrable_of_hasCompactSupport hasCompactSupport_baseKernel

theorem integral_baseKernel_pos : 0 < ∫ x : Space, baseKernel x := by
  rw [integral_pos_iff_support_of_nonneg baseKernel_nonneg integrable_baseKernel]
  have hball : (Metric.ball (0 : Space) (1 / 2 : ℝ)).Nonempty := ⟨0, by norm_num⟩
  apply lt_of_lt_of_le (Metric.isOpen_ball.measure_pos volume hball)
  apply measure_mono
  intro x hx
  have hn : ‖x‖ < 1 / 2 := by simpa using hx
  rw [Function.mem_support, baseKernel_eq_one hn.le]
  norm_num

noncomputable def kernelProfile (r : ℝ) : ℝ :=
  Real.smoothTransition (2 - 2 * r) / (∫ x : Space, baseKernel x)

noncomputable def kernel (x : Space) : ℝ := kernelProfile ‖x‖

theorem kernel_eq (x : Space) : kernel x = baseKernel x / (∫ y : Space, baseKernel y) := rfl

theorem contDiff_kernel : ContDiff ℝ ∞ kernel := contDiff_baseKernel.div_const _

theorem integral_kernel : ∫ x : Space, kernel x = 1 := by
  simp_rw [kernel_eq]
  rw [integral_div, div_self integral_baseKernel_pos.ne']

theorem kernel_zero_outside {x : Space} (hx : 1 ≤ ‖x‖) : kernel x = 0 := by
  rw [kernel_eq, baseKernel_eq_zero hx, zero_div]

theorem kernelProfile_nonneg (r : ℝ) : 0 ≤ kernelProfile r :=
  div_nonneg (Real.smoothTransition.nonneg _) integral_baseKernel_pos.le

theorem kernelProfile_le (r : ℝ) : kernelProfile r ≤ 1 / (∫ x : Space, baseKernel x) := by
  exact div_le_div_of_nonneg_right (Real.smoothTransition.le_one _) integral_baseKernel_pos.le

theorem continuous_kernelProfile : Continuous kernelProfile := by
  unfold kernelProfile
  exact (Real.smoothTransition.continuous.comp (continuous_const.sub
    (continuous_const.mul continuous_id))).div_const _

theorem kernelProfile_zero {r : ℝ} (hr : 1 ≤ r) : kernelProfile r = 0 := by
  unfold kernelProfile
  rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_div]

noncomputable def scaledKernelProfile (R r : ℝ) : ℝ := R⁻¹ ^ 3 * kernelProfile (r / R)

theorem scaledKernelProfile_nonneg {R : ℝ} (hR : 0 < R) (r : ℝ) :
    0 ≤ scaledKernelProfile R r :=
  mul_nonneg (by positivity) (kernelProfile_nonneg _)

theorem scaledKernelProfile_le {R : ℝ} (hR : 0 < R) (r : ℝ) :
    scaledKernelProfile R r ≤ R⁻¹ ^ 3 / (∫ x : Space, baseKernel x) := by
  dsimp [scaledKernelProfile]
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left (kernelProfile_le (r / R))
    (by positivity : (0 : ℝ) ≤ R⁻¹ ^ 3)

theorem scaledKernelProfile_zero {R r : ℝ} (hR : 0 < R) (hr : R ≤ r) :
    scaledKernelProfile R r = 0 := by
  unfold scaledKernelProfile
  rw [kernelProfile_zero ((le_div_iff₀ hR).mpr (by simpa using hr)), mul_zero]

theorem continuous_scaledKernelProfile (R : ℝ) : Continuous (scaledKernelProfile R) := by
  exact continuous_const.mul (continuous_kernelProfile.comp (continuous_id.div_const _))

def kernelHeight : ℝ := 1 / (∫ x : Space, baseKernel x)

theorem kernelHeight_pos : 0 < kernelHeight := one_div_pos.mpr integral_baseKernel_pos

theorem scaledKernelProfile_le_height {R : ℝ} (hR : 1 ≤ R) (r : ℝ) :
    scaledKernelProfile R r ≤ kernelHeight := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  calc
    _ ≤ R⁻¹ ^ 3 / (∫ x : Space, baseKernel x) := scaledKernelProfile_le hRp r
    _ ≤ kernelHeight := by
      unfold kernelHeight
      apply div_le_div_of_nonneg_right _ integral_baseKernel_pos.le
      exact pow_le_one₀ (inv_nonneg.mpr hRp.le) (inv_le_one_of_one_le₀ hR)

end
end ContinuumTemperature
end

end OAI
