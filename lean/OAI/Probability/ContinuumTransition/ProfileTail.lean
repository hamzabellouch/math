import OAI.Probability.ContinuumTransition.RadialKernel

namespace OAI

universe u_1

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature
noncomputable section
open scoped ContDiff

def attraction (t : ℝ) (σ R : ℕ → ℝ) (r : ℝ) : ℝ :=
  t * ∑' j, σ j * scaledKernelProfile (R j) r

theorem summable_attraction_terms {σ R : ℕ → ℝ}
    (hσ : ∀ j, 0 ≤ σ j) (hR : ∀ j, 1 ≤ R j) (hs : Summable σ) (r : ℝ) :
    Summable (fun j => σ j * scaledKernelProfile (R j) r) := by
  apply (hs.mul_right kernelHeight).of_norm_bounded
  intro j
  rw [Real.norm_of_nonneg (mul_nonneg (hσ j)
    (scaledKernelProfile_nonneg (lt_of_lt_of_le zero_lt_one (hR j)) r))]
  exact mul_le_mul_of_nonneg_left (scaledKernelProfile_le_height (hR j) r) (hσ j)

theorem attraction_nonneg {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ j, 0 ≤ σ j) (hR : ∀ j, 1 ≤ R j) (r : ℝ) :
    0 ≤ attraction t σ R r := by
  apply mul_nonneg ht
  exact tsum_nonneg (fun j => mul_nonneg (hσ j)
    (scaledKernelProfile_nonneg (lt_of_lt_of_le zero_lt_one (hR j)) r))

theorem attraction_le {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ j, 0 ≤ σ j) (hR : ∀ j, 1 ≤ R j) (hs : Summable σ) (r : ℝ) :
    attraction t σ R r ≤ t * (∑' j, σ j) * kernelHeight := by
  unfold attraction
  rw [mul_assoc, ← hs.tsum_mul_right]
  apply mul_le_mul_of_nonneg_left _ ht
  exact (summable_attraction_terms hσ hR hs r).tsum_le_tsum
    (fun j => mul_le_mul_of_nonneg_left (scaledKernelProfile_le_height (hR j) r) (hσ j))
    (hs.mul_right kernelHeight)

theorem continuous_attraction (t : ℝ) {σ R : ℕ → ℝ}
    (hσ : ∀ j, 0 ≤ σ j) (hR : ∀ j, 1 ≤ R j) (hs : Summable σ) :
    Continuous (attraction t σ R) := by
  apply continuous_const.mul
  apply continuous_tsum (fun j => continuous_const.mul (continuous_scaledKernelProfile (R j)))
    (hs.mul_right kernelHeight)
  intro j r
  change ‖σ j * scaledKernelProfile (R j) r‖ ≤ σ j * kernelHeight
  rw [Real.norm_of_nonneg (mul_nonneg (hσ j)
    (scaledKernelProfile_nonneg (lt_of_lt_of_le zero_lt_one (hR j)) r))]
  exact mul_le_mul_of_nonneg_left (scaledKernelProfile_le_height (hR j) r) (hσ j)

theorem weighted_scaledKernelProfile_le {R r : ℝ} (hR : 0 < R) (hr : 0 ≤ r) :
    r ^ 3 * scaledKernelProfile R r ≤ kernelHeight := by
  by_cases h : R ≤ r
  · rw [scaledKernelProfile_zero hR h, mul_zero]
    exact kernelHeight_pos.le
  · have hrR : r ≤ R := (lt_of_not_ge h).le
    calc
      _ ≤ r ^ 3 * (R⁻¹ ^ 3 / (∫ x : Space, baseKernel x)) :=
        mul_le_mul_of_nonneg_left (scaledKernelProfile_le hR r) (by positivity)
      _ = (r / R) ^ 3 * kernelHeight := by dsimp [kernelHeight]; ring
      _ ≤ 1 * kernelHeight := mul_le_mul_of_nonneg_right
        (pow_le_one₀ (div_nonneg hr hR.le) ((div_le_one hR).mpr hrR)) kernelHeight_pos.le
      _ = kernelHeight := one_mul _

theorem tendsto_weighted_attraction (t : ℝ) {σ R : ℕ → ℝ}
    (hσ : ∀ j, 0 ≤ σ j) (hR : ∀ j, 1 ≤ R j) (hs : Summable σ) :
    Tendsto (fun r => r ^ 3 * attraction t σ R r) atTop (𝓝 0) := by
  have hlim : Tendsto (fun r : ℝ => ∑' j, r ^ 3 *
      (σ j * scaledKernelProfile (R j) r)) atTop (𝓝 (∑' _j : ℕ, (0 : ℝ))) := by
    apply tendsto_tsum_of_dominated_convergence (hs.mul_right kernelHeight)
    · intro j
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (R j)] with r hr
      rw [scaledKernelProfile_zero (lt_of_lt_of_le zero_lt_one (hR j)) hr]
      simp
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr j
      rw [Real.norm_of_nonneg (mul_nonneg (by positivity)
        (mul_nonneg (hσ j) (scaledKernelProfile_nonneg
          (lt_of_lt_of_le zero_lt_one (hR j)) r)))]
      calc
        _ = σ j * (r ^ 3 * scaledKernelProfile (R j) r) := by ring
        _ ≤ σ j * kernelHeight := mul_le_mul_of_nonneg_left
          (weighted_scaledKernelProfile_le (lt_of_lt_of_le zero_lt_one (hR j)) hr) (hσ j)
  simp only [tsum_zero] at hlim
  have heq (r : ℝ) : r ^ 3 * attraction t σ R r =
      t * ∑' j, r ^ 3 * (σ j * scaledKernelProfile (R j) r) := by
    rw [tsum_mul_left]
    unfold attraction
    ring
  simp_rw [heq]
  simpa using hlim.const_mul t

def physicalProfile (t : ℝ) (σ R : ℕ → ℝ) (r : ℝ) : ℝ :=
  coreProfile t r - attraction t σ R r

theorem coreProfile_eq_zero {t r : ℝ} (ht : 1 < t) (hr : 1 ≤ r) :
    coreProfile t r = 0 := by
  have he : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hs : (1 + shellDelta) * Real.exp (-t) < 1 := by
    have ht' : Real.exp t > 1 + t := by simpa only [add_comm] using (Real.add_one_lt_exp (by linarith : t ≠ 0))
    rw [Real.exp_neg]
    unfold shellDelta
    apply (mul_inv_lt_iff₀ (Real.exp_pos t)).mpr
    linarith
  unfold coreProfile
  rw [ite_eq_right (by linarith), ite_eq_right (by linarith), ite_eq_right (not_lt.mpr hr)]

theorem physicalProfile_nonpos {t r : ℝ} (ht : 1 < t) {σ R : ℕ → ℝ}
    (hσ : ∀ j, 0 ≤ σ j) (hR : ∀ j, 1 ≤ R j) (hr : 1 ≤ r) :
    physicalProfile t σ R r ≤ 0 := by
  rw [physicalProfile, coreProfile_eq_zero ht hr, zero_sub]
  exact neg_nonpos.mpr (attraction_nonneg (by linarith) hσ hR r)

theorem physicalProfile_isLittleO {t : ℝ} (ht : 1 < t) {σ R : ℕ → ℝ}
    (hσ : ∀ j, 0 ≤ σ j) (hR : ∀ j, 1 ≤ R j) (hs : Summable σ) :
    Asymptotics.IsLittleO atTop (physicalProfile t σ R) (fun r : ℝ => r ^ (-3 : ℤ)) := by
  apply Asymptotics.isLittleO_of_tendsto'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact fun h => False.elim ((zpow_ne_zero _ hr.ne') h)
  · have hl : Tendsto (fun r => -(r ^ 3 * attraction t σ R r)) atTop (𝓝 0) := by
      simpa only [neg_zero] using (tendsto_weighted_attraction t hσ hR hs).neg
    apply hl.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    rw [physicalProfile, coreProfile_eq_zero ht hr, zero_sub]
    simp only [zpow_neg, zpow_ofNat, div_inv_eq_mul]
    ring

theorem integrable_tsum_real {α : Type u_1} [MeasurableSpace α] {μ : Measure α}
    (F : ℕ → α → ℝ) (hF : ∀ j, Integrable (F j) μ)
    (hs : Summable (fun j => ∫ x, ‖F j x‖ ∂μ)) :
    Integrable (fun x => ∑' j, F j x) μ := by
  refine ⟨(AEMeasurable.tsum (fun j => (hF j).aemeasurable)).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  calc
    _ ≤ ∫⁻ x, ∑' j, ‖F j x‖ₑ ∂μ := lintegral_mono (fun x => enorm_tsum_le_tsum_enorm)
    _ = ∑' j, ∫⁻ x, ‖F j x‖ₑ ∂μ :=
      lintegral_tsum (fun j => (hF j).aemeasurable.enorm)
    _ = ∑' j, ENNReal.ofReal (∫ x, ‖F j x‖ ∂μ) := by
      congr 1
      funext j
      exact (ofReal_integral_norm_eq_lintegral_enorm (hF j)).symm
    _ < ⊤ := hs.tsum_ofReal_lt_top

def radialWeighted (R r : ℝ) : ℝ :=
  (Icc (0 : ℝ) R).indicator (fun s => s ^ 2 * scaledKernelProfile R s) r

theorem radialWeighted_nonneg {R : ℝ} (hR : 0 < R) (r : ℝ) :
    0 ≤ radialWeighted R r := by
  apply Set.indicator_nonneg
  intro s _
  exact mul_nonneg (sq_nonneg s) (scaledKernelProfile_nonneg hR s)

theorem radialWeighted_eq {R r : ℝ} (hR : 0 < R) (hr : 0 ≤ r) :
    radialWeighted R r = r ^ 2 * scaledKernelProfile R r := by
  by_cases hh : r ≤ R
  · exact Set.indicator_of_mem (show r ∈ Icc (0 : ℝ) R from ⟨hr, hh⟩) _
  · rw [radialWeighted, Set.indicator_of_notMem (fun h => hh h.2),
      scaledKernelProfile_zero hR (le_of_not_ge hh), mul_zero]

theorem integrable_radialWeighted (R : ℝ) : Integrable (radialWeighted R) := by
  apply (integrable_indicator_iff measurableSet_Icc).mpr
  exact (continuous_id.pow 2 |>.mul (continuous_scaledKernelProfile R)).integrableOn_Icc

theorem integral_radialWeighted_le {R : ℝ} (hR : 0 < R) :
    ∫ r : ℝ, radialWeighted R r ≤ kernelHeight / 3 := by
  let F : ℝ → ℝ := fun r => (Icc (0 : ℝ) R).indicator
    (fun s => s ^ 2 * (R⁻¹ ^ 3 * kernelHeight)) r
  have hFi : Integrable F := by
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    exact (continuous_id.pow 2 |>.mul continuous_const).integrableOn_Icc
  have hbound : ∀ r, radialWeighted R r ≤ F r := by
    intro r
    apply Set.indicator_le_indicator
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg r)
    simpa only [kernelHeight, div_eq_mul_inv, one_mul] using scaledKernelProfile_le hR r
  apply (integral_mono (integrable_radialWeighted R) hFi hbound).trans_eq
  dsimp [F]
  rw [integral_indicator measurableSet_Icc, integral_mul_const,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hR.le,
    integral_pow]
  dsimp [kernelHeight]
  norm_num
  field_simp

theorem integrable_weighted_attraction (t : ℝ) {σ R : ℕ → ℝ}
    (hσ : ∀ j, 0 ≤ σ j) (hR : ∀ j, 1 ≤ R j) (hs : Summable σ) :
    IntegrableOn (fun r => r ^ 2 * attraction t σ R r) (Ioi (0 : ℝ)) := by
  have hi (j : ℕ) : Integrable (fun r => σ j * radialWeighted (R j) r) :=
    (integrable_radialWeighted (R j)).const_mul (σ j)
  have hs' : Summable (fun j => ∫ r : ℝ, ‖σ j * radialWeighted (R j) r‖) := by
    apply Summable.of_nonneg_of_le (fun j => integral_nonneg (fun _ => norm_nonneg _)) _
      (hs.mul_right (kernelHeight / 3))
    intro j
    simp_rw [Real.norm_of_nonneg (mul_nonneg (hσ j)
      (radialWeighted_nonneg (lt_of_lt_of_le zero_lt_one (hR j)) _))]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (integral_radialWeighted_le (lt_of_lt_of_le zero_lt_one (hR j))) (hσ j)
  apply ((integrable_tsum_real _ hi hs').const_mul t).integrableOn.congr_fun _ measurableSet_Ioi
  intro r hr
  simp only [attraction]
  simp_rw [radialWeighted_eq (lt_of_lt_of_le zero_lt_one (hR _)) (le_of_lt hr)]
  rw [show (fun j => σ j * (r ^ 2 * scaledKernelProfile (R j) r)) =
      (fun j => r ^ 2 * (σ j * scaledKernelProfile (R j) r)) by funext j; ring,
    tsum_mul_left]
  ring

end
end ContinuumTemperature
end

end OAI
