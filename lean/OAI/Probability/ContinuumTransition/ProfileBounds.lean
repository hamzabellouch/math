import OAI.Probability.ContinuumTransition.ProfileTail

namespace OAI

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature
noncomputable section
open scoped ContDiff

theorem measurable_coreProfile (t : ℝ) : Measurable (coreProfile t) := by
  unfold coreProfile
  apply Measurable.ite (measurableSet_lt measurable_id measurable_const)
    (measurable_const.add ((measurable_const.div measurable_id).pow_const 12))
  apply Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
    measurable_const measurable_const

theorem coreProfile_nonneg (t r : ℝ) : 0 ≤ coreProfile t r := by
  unfold coreProfile
  split_ifs <;> positivity

theorem coreProfile_le {a r : ℝ} (ha : 0 < a) (har : a ≤ r) (t : ℝ) :
    coreProfile t r ≤ t ^ 2 + (Real.exp (-t) / a) ^ 12 := by
  have hdiv : Real.exp (-t) / r ≤ Real.exp (-t) / a :=
    div_le_div_of_nonneg_left (Real.exp_pos _).le ha har
  have hp := pow_le_pow_left₀ (div_nonneg (Real.exp_pos _).le (ha.le.trans har)) hdiv 12
  unfold coreProfile
  split_ifs <;> nlinarith [sq_nonneg t, even_two_mul 6 |>.pow_nonneg (Real.exp (-t) / a)]

theorem measurable_physicalProfile (t : ℝ) {σ R : ℕ → ℝ}
    (hσ : ∀ j, 0 ≤ σ j) (hR : ∀ j, 1 ≤ R j) (hs : Summable σ) :
    Measurable (physicalProfile t σ R) :=
  (measurable_coreProfile t).sub (continuous_attraction t hσ hR hs).measurable

theorem measurable_radialPotential {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Measurable (radialPotential φ) := by
  apply Measurable.ite (measurableSet_singleton (0 : Space)) measurable_const
  exact measurable_coe_real_ereal.comp (hφ.comp measurable_norm)

theorem physicalProfile_locally_bounded {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ j, 0 ≤ σ j) (hR : ∀ j, 1 ≤ R j) (hs : Summable σ)
    {a b : ℝ} (ha : 0 < a) :
    BddAbove (physicalProfile t σ R '' Icc a b) ∧
      BddBelow (physicalProfile t σ R '' Icc a b) := by
  constructor
  · refine ⟨t ^ 2 + (Real.exp (-t) / a) ^ 12, ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    exact (sub_le_self _ (attraction_nonneg ht hσ hR r)).trans (coreProfile_le ha hr.1 t)
  · refine ⟨-(t * (∑' j, σ j) * kernelHeight), ?_⟩
    rintro _ ⟨r, _, rfl⟩
    dsimp [physicalProfile]
    have := attraction_le ht hσ hR hs r
    linarith [coreProfile_nonneg t r]

theorem physicalProfile_tendsto_zero {t : ℝ} (ht : 0 ≤ t) {σ R : ℕ → ℝ}
    (hσ : ∀ j, 0 ≤ σ j) (hR : ∀ j, 1 ≤ R j) (hs : Summable σ) :
    Tendsto (physicalProfile t σ R) (𝓝[>] (0 : ℝ)) atTop := by
  let C := t * (∑' j, σ j) * kernelHeight
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg ht (tsum_nonneg hσ)) kernelHeight_pos.le
  apply tendsto_atTop.2
  intro M
  let K := |M| + C + 2
  have hK : 1 < K := by dsimp [K]; linarith [abs_nonneg M]
  have he := Real.exp_pos (-t)
  have hε : 0 < Real.exp (-t) / K := div_pos he (by linarith)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hε).filter_mono nhdsWithin_le_nhds] with r hr hrε
  have hrp : 0 < r := hr
  have hεe : Real.exp (-t) / K < Real.exp (-t) := (div_lt_self he hK)
  have hrr : r < Real.exp (-t) := hrε.trans hεe
  have hinv : K < Real.exp (-t) / r := (lt_div_iff₀ hrp).mpr
    (by have hh := (lt_div_iff₀ (show 0 < K by linarith)).mp hrε; nlinarith)
  have hp : Real.exp (-t) / r ≤ (Real.exp (-t) / r) ^ 12 :=
    le_self_pow₀ (by linarith) (by norm_num)
  rw [physicalProfile, coreProfile, ite_eq_left hrr]
  have hbound := attraction_le ht hσ hR hs r
  dsimp [C, K] at *
  nlinarith [sq_nonneg t, le_abs_self M]

theorem scaledKernelProfile_eq_height {R r : ℝ} (hR : 0 < R) (hr : r ≤ R / 2) :
    scaledKernelProfile R r = R⁻¹ ^ 3 * kernelHeight := by
  have hh : 1 ≤ 2 - 2 * (r / R) := by
    have hh : r / R ≤ (1 / 2 : ℝ) := (div_le_iff₀ hR).mpr (by linarith)
    linarith
  simp only [scaledKernelProfile, kernelProfile, Real.smoothTransition.one_of_one_le hh,
    kernelHeight]

theorem physicalProfile_negative_annulus {t : ℝ} (ht : 1 < t) {σ R : ℕ → ℝ}
    (hσ : ∀ j, 0 ≤ σ j) (hR : ∀ j, 1 ≤ R j) (hs : Summable σ)
    (hσ0 : 0 < σ 0) (hR0 : 4 ≤ R 0) :
    ∃ a : ℝ, 0 < a ∧ ∀ r ∈ Icc (1 : ℝ) 2, physicalProfile t σ R r ≤ -a := by
  refine ⟨t * σ 0 * (R 0)⁻¹ ^ 3 * kernelHeight, ?_, ?_⟩
  · exact mul_pos (mul_pos (mul_pos (by linarith) hσ0)
      (pow_pos (inv_pos.mpr (by linarith)) _)) kernelHeight_pos
  intro r hr
  obtain ⟨hr1, hr2⟩ := hr
  rw [physicalProfile, coreProfile_eq_zero ht hr1, zero_sub]
  apply neg_le_neg
  have hterm := (summable_attraction_terms hσ hR hs r).le_tsum 0
    (fun j _ => mul_nonneg (hσ j)
      (scaledKernelProfile_nonneg (lt_of_lt_of_le zero_lt_one (hR j)) r))
  rw [scaledKernelProfile_eq_height (by linarith : 0 < R 0) (by linarith : r ≤ R 0 / 2)] at hterm
  have hh := mul_le_mul_of_nonneg_left hterm (by linarith : 0 ≤ t)
  simpa only [attraction, mul_assoc] using hh

theorem integrable_weighted_physicalProfile {t : ℝ} (ht : 1 < t) {σ R : ℕ → ℝ}
    (hσ : ∀ j, 0 ≤ σ j) (hR : ∀ j, 1 ≤ R j) (hs : Summable σ) :
    IntegrableOn (fun r : ℝ => r ^ 2 * |physicalProfile t σ R r|) (Ioi (1 : ℝ)) := by
  apply ((integrable_weighted_attraction t hσ hR hs).mono_set
    (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))).congr_fun _ measurableSet_Ioi
  intro r hr
  simp only [physicalProfile, coreProfile_eq_zero ht (le_of_lt hr), zero_sub, abs_neg,
    abs_of_nonneg (attraction_nonneg (by linarith) hσ hR r)]

end
end ContinuumTemperature
end

end OAI
