import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import OAI.NumberTheory.Jacobsthal.Probability.FirstHitKernels

namespace OAI

namespace Erdos970

section

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
namespace Erdos970Dependency.InvariantDensities
open NumberTheoryLean NumberTheoryLean.BuchstabBridge NumberTheoryLean.DerivativeWeights
open NumberTheoryLean.TransitionKernels NumberTheoryLean.FinitePathGeometry

noncomputable def oddFactor (s : ℝ) : ℝ := 1 - 1 / s ^ 2
noncomputable def evenDensity (s : ℝ) : ℝ := (Ici (2 : ℝ)).indicator phiEven s
noncomputable def oddDensity (s : ℝ) : ℝ := (Ici (1 : ℝ)).indicator (fun t ↦ oddFactor t * phiOdd t) s

theorem oddFactor_bounds {s : ℝ} (hs : 1 ≤ s) : 0 ≤ oddFactor s ∧ oddFactor s ≤ 1 := by
  have hs0 : 0 < s := by linarith
  have hsq : 1 ≤ s ^ 2 := by nlinarith
  have hinv : 1 / s ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos hs0)).mpr hsq
  have hnonneg : 0 ≤ 1 / s ^ 2 := by positivity
  unfold oddFactor
  constructor <;> linarith

theorem oddFactor_pos {s : ℝ} (hs : 1 < s) : 0 < oddFactor s := by
  unfold oddFactor
  have hs0 : 0 < s := by linarith
  have : 1 / s ^ 2 < 1 := (div_lt_one (sq_pos_of_pos hs0)).mpr (by nlinarith)
  linarith

theorem oddFactor_measurable : Measurable oddFactor := by
  unfold oddFactor
  fun_prop

theorem evenDensity_measurable : Measurable evenDensity :=
  phiEven_measurable.indicator measurableSet_Ici

theorem oddDensity_measurable : Measurable oddDensity :=
  (oddFactor_measurable.mul phiOdd_continuous.measurable).indicator measurableSet_Ici

theorem evenDensity_nonneg (s : ℝ) : 0 ≤ evenDensity s := by
  by_cases hs : 2 ≤ s
  · rw [evenDensity, indicator_of_mem (show s ∈ Ici (2 : ℝ) from hs)]
    exact (phiEven_pos (by linarith)).le
  · rw [evenDensity, indicator_of_notMem (show s ∉ Ici (2 : ℝ) from hs)]

theorem oddDensity_nonneg (s : ℝ) : 0 ≤ oddDensity s := by
  by_cases hs : 1 ≤ s
  · rw [oddDensity, indicator_of_mem (show s ∈ Ici (1 : ℝ) from hs)]
    exact mul_nonneg (oddFactor_bounds hs).1 (phiOdd_pos s).le
  · rw [oddDensity, indicator_of_notMem (show s ∉ Ici (1 : ℝ) from hs)]

theorem oddFactor_hasDerivAt {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (fun t : ℝ ↦ t + 1 / t) (oddFactor s) s := by
  have h := (hasDerivAt_id s).add ((hasDerivAt_const s (1 : ℝ)).div (hasDerivAt_id s) hs)
  convert! h using 1
  simp only [oddFactor, id_eq, zero_mul, zero_sub, mul_one]
  ring

theorem integral_oddFactor {b : ℝ} (hb : 1 ≤ b) :
    (∫ s in (1 : ℝ)..b, oddFactor s) = b + 1 / b - 2 := by
  have hd : ∀ s ∈ uIcc (1 : ℝ) b,
      HasDerivAt (fun t : ℝ ↦ t + 1 / t) (oddFactor s) s := by
    intro s hs
    rw [uIcc_of_le hb] at hs
    exact oddFactor_hasDerivAt (by linarith [hs.1])
  have hi : IntervalIntegrable oddFactor volume 1 b := by
    apply ContinuousOn.intervalIntegrable
    intro s hs
    rw [uIcc_of_le hb] at hs
    apply ContinuousAt.continuousWithinAt
    unfold oddFactor
    exact continuousAt_const.sub (continuousAt_const.div (continuousAt_id.pow 2) (by nlinarith [hs.1]))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  norm_num at h
  simpa only [one_div] using h

noncomputable def beta : ℝ := ∫ s in (1 : ℝ)..3, oddDensity s

theorem beta_eq : beta = 4 * sieveA / 3 := by
  unfold beta
  calc
    (∫ s in (1 : ℝ)..3, oddDensity s) = ∫ s in (1 : ℝ)..3, sieveA * oddFactor s := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] at hs
      rw [oddDensity, indicator_of_mem (show s ∈ Ici (1 : ℝ) from hs.1), phiOdd_initial hs.2, mul_comm]
    _ = sieveA * (3 + 1 / 3 - 2) := by
      rw [intervalIntegral.integral_const_mul, integral_oddFactor (by norm_num)]
    _ = _ := by ring

theorem beta_pos : 0 < beta := by
  rw [beta_eq]
  exact div_pos (mul_pos (by norm_num) sieveA_pos) (by norm_num)

end Erdos970Dependency.InvariantDensities

end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Erdos970Dependency.InvariantFiniteness
open NumberTheoryLean NumberTheoryLean.DerivativeWeights NumberTheoryLean.TransitionKernels
open Erdos970Dependency.InvariantDensities

theorem integrableOn_Ici_of_exp_tail {f : ℝ → ℝ} {a : ℝ}
    (hm : Measurable f) (hc : ContinuousOn f (Ici a)) (hn : ∀ s, a ≤ s → 0 ≤ f s)
    {C T : ℝ} (hT : a ≤ T) (hb : ∀ s, T ≤ s → f s ≤ C * Real.exp (-s)) :
    IntegrableOn f (Ici a) := by
  have hcompact : IntegrableOn f (Icc a T) :=
    (hc.mono Icc_subset_Ici_self).integrableOn_Icc
  have htail : IntegrableOn f (Ioi T) := by
    apply ((integrableOn_exp_neg_Ioi T).const_mul C).mono_nonneg hm.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact hn s (hT.trans hs.le)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact hb s hs.le
  rw [← Icc_union_Ioi_eq_Ici hT]
  exact hcompact.union htail

theorem weights_exp_majorant : ∃ D U : ℝ, 0 < D ∧ 2 ≤ U ∧ ∀ s : ℝ, U ≤ s →
    phiEven s ≤ D * Real.exp (-s) ∧ phiOdd s ≤ D * Real.exp (-s) := by
  obtain ⟨c, C, hc, hC, hphi⟩ := WeightDickmanComparison.weights_dickman_bounds
  obtain ⟨R, hR, T, hT, hrho⟩ := DickmanDecay.rho_exponential_majorant 1
  refine ⟨C * R * Real.exp 2, T + 2, by positivity, by linarith, ?_⟩
  intro s hs
  have hs2 : 2 ≤ s := by linarith
  have hr := hrho (s - 2) (by linarith)
  have heq : Real.exp (-(s - 2)) = Real.exp 2 * Real.exp (-s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [neg_one_mul, heq] at hr
  have hbound : C * Dickman.rho (s - 2) ≤ (C * R * Real.exp 2) * Real.exp (-s) := by
    have h := mul_le_mul_of_nonneg_left hr hC.le
    convert! h using 1
    ring
  exact ⟨(hphi s hs2).1.2.trans hbound, (hphi s hs2).2.2.trans hbound⟩

theorem phiEven_integrableOn : IntegrableOn phiEven (Ici (2 : ℝ)) := by
  obtain ⟨D, U, _, hU, hb⟩ := weights_exp_majorant
  apply integrableOn_Ici_of_exp_tail phiEven_measurable ?_
    (fun s hs ↦ (phiEven_pos (by linarith)).le) hU (fun s hs ↦ (hb s hs).1)
  intro s hs
  exact (phiEven_continuousAt (by change (2 : ℝ) ≤ s at hs; linarith)).continuousWithinAt

theorem phiOdd_integrableOn : IntegrableOn phiOdd (Ici (1 : ℝ)) := by
  obtain ⟨D, U, _, hU, hb⟩ := weights_exp_majorant
  exact integrableOn_Ici_of_exp_tail phiOdd_continuous.measurable phiOdd_continuous.continuousOn
    (fun s _ ↦ (phiOdd_pos s).le) (show (1 : ℝ) ≤ U by linarith) (fun s hs ↦ (hb s hs).2)

theorem evenDensity_integrable : Integrable InvariantDensities.evenDensity :=
  (integrable_indicator_iff measurableSet_Ici).mpr phiEven_integrableOn

theorem oddDensity_integrable : Integrable InvariantDensities.oddDensity := by
  apply (integrable_indicator_iff measurableSet_Ici).mpr
  apply phiOdd_integrableOn.mono_nonneg
    (oddFactor_measurable.mul phiOdd_continuous.measurable).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
    exact mul_nonneg (oddFactor_bounds hs).1 (phiOdd_pos s).le
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with s hs
    have h := mul_le_mul_of_nonneg_right (oddFactor_bounds hs).2 (phiOdd_pos s).le
    convert! h using 1
    simp only [one_mul]

noncomputable def evenMeasure : Measure ℝ := volume.withDensity (fun s ↦ ENNReal.ofReal (InvariantDensities.evenDensity s))
noncomputable def oddMeasure : Measure ℝ := volume.withDensity (fun s ↦ ENNReal.ofReal (InvariantDensities.oddDensity s))

instance evenMeasure_isFiniteMeasure : IsFiniteMeasure evenMeasure := by
  constructor
  rw [evenMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal evenDensity_integrable
      (Filter.Eventually.of_forall InvariantDensities.evenDensity_nonneg)]
  exact ENNReal.ofReal_lt_top

instance oddMeasure_isFiniteMeasure : IsFiniteMeasure oddMeasure := by
  constructor
  rw [oddMeasure, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal oddDensity_integrable
      (Filter.Eventually.of_forall InvariantDensities.oddDensity_nonneg)]
  exact ENNReal.ofReal_lt_top

end Erdos970Dependency.InvariantFiniteness

end

end Erdos970

end OAI
