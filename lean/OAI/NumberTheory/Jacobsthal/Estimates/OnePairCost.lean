import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import OAI.NumberTheory.Jacobsthal.Analysis.DeficitIntegralValues
import OAI.NumberTheory.Jacobsthal.Renewal.OccupationAge

namespace OAI

namespace Erdos970

section

open Set MeasureTheory
namespace Erdos970Dependency.InvariantCostBound
open NumberTheoryLean NumberTheoryLean.BuchstabBridge NumberTheoryLean.DerivativeWeights
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.FinitePathMeasures
open NumberTheoryLean.NormalizedDeficits NumberTheoryLean.DeficitFutureIntegrals
open Erdos970Dependency.InvariantDensities Erdos970Dependency.DeficitIntegralValues

noncomputable def evenCost (s : ℝ) : ℝ := evenDensity s * cost s
noncomputable def oddCost (s : ℝ) : ℝ := oddDensity s * cost s
noncomputable def evenMajor : ℝ → ℝ := (Ici (2 : ℝ)).indicator (fun s ↦ lowerDeficit s + upperDeficit (s - 1))
noncomputable def oddMajor : ℝ → ℝ := (Ici (1 : ℝ)).indicator (fun s ↦ upperDeficit s + lowerDeficit (s - 1))

theorem cost_le_inv {s : ℝ} (hs : 0 < s) : cost s ≤ 1 / s := by
  have h := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / s by positivity)
  change Real.log (1 + 1 / s) ≤ 1 / s
  linarith

theorem evenCost_nonneg (s : ℝ) : 0 ≤ evenCost s := by
  by_cases hs : 2 ≤ s
  · rw [evenCost, evenDensity, indicator_of_mem (show s ∈ Ici (2 : ℝ) from hs)]
    exact mul_nonneg (phiEven_pos (by linarith)).le (cost_pos (by linarith)).le
  · rw [evenCost, evenDensity, indicator_of_notMem (show s ∉ Ici (2 : ℝ) from hs), zero_mul]

theorem oddCost_nonneg (s : ℝ) : 0 ≤ oddCost s := by
  by_cases hs : 1 ≤ s
  · rw [oddCost]
    exact mul_nonneg (oddDensity_nonneg s) (cost_pos (by linarith)).le
  · rw [oddCost, oddDensity, indicator_of_notMem (show s ∉ Ici (1 : ℝ) from hs), zero_mul]

theorem evenCost_le_major (s : ℝ) : evenCost s ≤ evenMajor s := by
  by_cases hs : 2 ≤ s
  · rw [evenCost, evenDensity, evenMajor,
      indicator_of_mem (show s ∈ Ici (2 : ℝ) from hs), indicator_of_mem (show s ∈ Ici (2 : ℝ) from hs)]
    calc
      phiEven s * cost s ≤ phiEven s * (1 / s) :=
        mul_le_mul_of_nonneg_left (cost_le_inv (by linarith)) (phiEven_pos (by linarith)).le
      _ = _ := by rw [phiEven_eq_deficits hs]; field_simp
  · rw [evenCost, evenDensity, evenMajor,
      indicator_of_notMem (show s ∉ Ici (2 : ℝ) from hs),
      indicator_of_notMem (show s ∉ Ici (2 : ℝ) from hs), zero_mul]

theorem oddCost_le_major (s : ℝ) : oddCost s ≤ oddMajor s := by
  by_cases hs : 1 ≤ s
  · rw [oddCost, oddDensity, oddMajor,
      indicator_of_mem (show s ∈ Ici (1 : ℝ) from hs), indicator_of_mem (show s ∈ Ici (1 : ℝ) from hs)]
    have hphi : oddFactor s * phiOdd s ≤ phiOdd s := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (oddFactor_bounds hs).2 (phiOdd_pos s).le
    calc
      (oddFactor s * phiOdd s) * cost s ≤ phiOdd s * cost s :=
        mul_le_mul_of_nonneg_right hphi (cost_pos (by linarith)).le
      _ ≤ phiOdd s * (1 / s) :=
        mul_le_mul_of_nonneg_left (cost_le_inv (by linarith)) (phiOdd_pos s).le
      _ = _ := by rw [phiOdd_eq_deficits hs]; field_simp
  · rw [oddCost, oddDensity, oddMajor,
      indicator_of_notMem (show s ∉ Ici (1 : ℝ) from hs),
      indicator_of_notMem (show s ∉ Ici (1 : ℝ) from hs), zero_mul]

theorem evenMajor_integrable : Integrable evenMajor :=
  (integrable_indicator_iff measurableSet_Ici).mpr even_majorant_integral.1

theorem oddMajor_integrable : Integrable oddMajor :=
  (integrable_indicator_iff measurableSet_Ici).mpr odd_majorant_integral.1

theorem evenCost_integrable : Integrable evenCost := by
  apply evenMajor_integrable.mono' (evenDensity_measurable.mul cost_measurable).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun s ↦ by
    change ‖evenCost s‖ ≤ evenMajor s
    rw [Real.norm_of_nonneg (evenCost_nonneg s)]
    exact evenCost_le_major s)

theorem oddCost_integrable : Integrable oddCost := by
  apply oddMajor_integrable.mono' (oddDensity_measurable.mul cost_measurable).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun s ↦ by
    change ‖oddCost s‖ ≤ oddMajor s
    rw [Real.norm_of_nonneg (oddCost_nonneg s)]
    exact oddCost_le_major s)

theorem even_cost_bound : (∫ s, evenCost s) ≤ sieveA - 1 := by
  have h := integral_mono evenCost_integrable evenMajor_integrable evenCost_le_major
  rw [evenMajor, integral_indicator measurableSet_Ici, even_majorant_integral.2] at h
  exact h

theorem odd_cost_bound : (∫ s, oddCost s) ≤ sieveA + 1 := by
  have h := integral_mono oddCost_integrable oddMajor_integrable oddCost_le_major
  rw [oddMajor, integral_indicator measurableSet_Ici, odd_majorant_integral.2] at h
  exact h

theorem even_cost_pos : 0 < ∫ s, evenCost s := by
  apply (integral_pos_iff_support_of_nonneg evenCost_nonneg evenCost_integrable).mpr
  have hsub : Icc (2 : ℝ) 3 ⊆ Function.support evenCost := by
    intro s hs
    apply ne_of_gt
    rw [evenCost, evenDensity, indicator_of_mem (show s ∈ Ici (2 : ℝ) from hs.1)]
    exact mul_pos (phiEven_pos (by linarith [hs.1])) (cost_pos (by linarith [hs.1]))
  exact lt_of_lt_of_le (by norm_num [Real.volume_Icc] : 0 < volume (Icc (2 : ℝ) 3)) (measure_mono hsub)

noncomputable def costMass : ℝ := (∫ s, evenCost s) + ∫ s, oddCost s

theorem costMass_pos : 0 < costMass :=
  add_pos_of_pos_of_nonneg even_cost_pos (integral_nonneg oddCost_nonneg)

theorem costMass_le : costMass ≤ 2 * sieveA := by
  unfold costMass
  linarith [even_cost_bound, odd_cost_bound]

end Erdos970Dependency.InvariantCostBound

end

section

open Set MeasureTheory ProbabilityTheory
namespace Erdos970Dependency.RawStateCost
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.FinitePathMeasures NumberTheoryLean.CycleCostMoments
open NumberTheoryLean.CycleOccupation
open Erdos970Dependency.InvariantDensities Erdos970Dependency.InvariantFiniteness
open Erdos970Dependency.OrdinaryKernelInvariance Erdos970Dependency.StateKernelInvariance
open Erdos970Dependency.InvariantCostBound Erdos970Dependency.ActualCycleOccupation

noncomputable def stateCost (s : State) : ℝ := cost (stateRatio s)

theorem stateCost_measurable : Measurable stateCost := cost_measurable.comp stateRatio_measurable

theorem stateCost_bounds (s : State) : 0 < stateCost s ∧ stateCost s ≤ Real.log 3 := by
  have hs : 1 / 2 ≤ stateRatio s := by
    cases s with
    | inl s => change 1 / 2 ≤ s.1; linarith [s.2]
    | inr s => change 1 / 2 ≤ s.1; linarith [s.2]
  exact ⟨cost_pos (by linarith), draw_cost_le_log_three hs⟩

theorem stateCost_integrable (mu : Measure State) [IsFiniteMeasure mu] : Integrable stateCost mu := by
  apply (integrable_const (Real.log 3)).mono' stateCost_measurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun s ↦ by
    rw [Real.norm_of_nonneg (stateCost_bounds s).1.le]
    exact (stateCost_bounds s).2)

theorem integral_evenMeasure (g : ℝ → ℝ) : (∫ s, g s ∂evenMeasure) =
    ∫ s, InvariantDensities.evenDensity s * g s := by
  have h := integral_withDensity_eq_integral_toReal_smul (μ := (volume : Measure ℝ))
    (ENNReal.measurable_ofReal.comp InvariantDensities.evenDensity_measurable)
    (Filter.Eventually.of_forall (fun _ : ℝ ↦ ENNReal.ofReal_lt_top)) g
  simpa only [evenMeasure, Function.comp_def, ENNReal.toReal_ofReal (InvariantDensities.evenDensity_nonneg _),
    smul_eq_mul] using h

theorem integral_oddMeasure (g : ℝ → ℝ) : (∫ s, g s ∂oddMeasure) =
    ∫ s, InvariantDensities.oddDensity s * g s := by
  have h := integral_withDensity_eq_integral_toReal_smul (μ := (volume : Measure ℝ))
    (ENNReal.measurable_ofReal.comp InvariantDensities.oddDensity_measurable)
    (Filter.Eventually.of_forall (fun _ : ℝ ↦ ENNReal.ofReal_lt_top)) g
  simpa only [oddMeasure, Function.comp_def, ENNReal.toReal_ofReal (InvariantDensities.oddDensity_nonneg _),
    smul_eq_mul] using h

theorem even_lifted_cost (s : ℝ) : InvariantDensities.evenDensity s * cost (evenLift s).1 = evenCost s := by
  by_cases hs : 2 ≤ s
  · have heq : (evenLift s).1 = s := max_eq_right (by linarith)
    rw [heq]
    rfl
  · rw [evenCost, InvariantDensities.evenDensity,
      indicator_of_notMem (show s ∉ Ici (2 : ℝ) from hs), zero_mul, zero_mul]

theorem odd_lifted_cost (s : ℝ) : InvariantDensities.oddDensity s * cost (oddLift s).1 = oddCost s := by
  by_cases hs : 1 ≤ s
  · have heq : (oddLift s).1 = s := max_eq_right (by linarith)
    rw [heq]
    rfl
  · rw [oddCost, InvariantDensities.oddDensity,
      indicator_of_notMem (show s ∉ Ici (1 : ℝ) from hs), zero_mul, zero_mul]

theorem state_cost_integral : (∫ s, stateCost s ∂stateMeasure) = costMass := by
  rw [stateMeasure, integral_add_measure (stateCost_integrable _) (stateCost_integrable _),
    integral_map measurable_inl.aemeasurable stateCost_measurable.aestronglyMeasurable,
    integral_map measurable_inr.aemeasurable stateCost_measurable.aestronglyMeasurable]
  simp only [stateCost, stateRatio, Sum.elim_inl, Sum.elim_inr]
  have he := integral_map (μ := evenMeasure) evenLift_measurable.aemeasurable
    (cost_measurable.comp (measurable_subtype_coe : Measurable
      (Subtype.val : NumberTheoryLean.TransitionKernels.EvenState → ℝ))).aestronglyMeasurable
  have ho := integral_map (μ := oddMeasure) oddLift_measurable.aemeasurable
    (cost_measurable.comp (measurable_subtype_coe : Measurable
      (Subtype.val : NumberTheoryLean.TransitionKernels.OddState → ℝ))).aestronglyMeasurable
  simp only [Function.comp_def] at he ho
  rw [evenStateMeasure, he, oddStateMeasure, ho, integral_evenMeasure, integral_oddMeasure]
  simp_rw [even_lifted_cost, odd_lifted_cost]
  rfl

theorem occupation_increment_integrable :
    Integrable (fun y : CostState ↦ stateCost y.1) occupationMeasure :=
  (integrable_state_occupation_iff stateCost_measurable).mp (stateCost_integrable stateMeasure)

theorem occupation_increment_integral :
    (∫ y : CostState, stateCost y.1 ∂occupationMeasure) = costMass / beta := by
  have h := (integral_state_occupation stateCost_measurable occupation_increment_integrable).2
  rw [state_cost_integral] at h
  simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using h

end Erdos970Dependency.RawStateCost

end

section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace Erdos970Dependency.OnePairCost
open NumberTheoryLean.TransitionKernels NumberTheoryLean.FinitePathGeometry NumberTheoryLean.FinitePathMeasures
open NumberTheoryLean.PairedCostProcess NumberTheoryLean.CostReturnLaw NumberTheoryLean.CycleOccupation
open Erdos970Dependency.RawStateCost

noncomputable def pairIncrement (z : OddCost) : ℝ≥0∞ :=
  ∫⁻ y : CostState, ENNReal.ofReal (stateCost y.1) ∂pairVisits z

theorem increment_test_measurable : Measurable (fun y : CostState ↦ ENNReal.ofReal (stateCost y.1)) :=
  ENNReal.measurable_ofReal.comp (stateCost_measurable.comp measurable_fst)

theorem age_test_measurable : Measurable (fun y : OddCost ↦ ENNReal.ofReal y.2) :=
  ENNReal.measurable_ofReal.comp measurable_snd

theorem pairIncrement_measurable : Measurable pairIncrement := increment_test_measurable.lintegral_kernel

theorem even_increment_measurable :
    Measurable (fun x : EvenState × OddState ↦ ENNReal.ofReal (cost x.1.1)) :=
  ENNReal.measurable_ofReal.comp (cost_measurable.comp (measurable_subtype_coe.comp measurable_fst))

theorem odd_increment_measurable :
    Measurable (fun x : EvenState × OddState ↦ ENNReal.ofReal (cost x.2.1)) :=
  ENNReal.measurable_ofReal.comp (cost_measurable.comp (measurable_subtype_coe.comp measurable_snd))

theorem pairIncrement_formula (z : OddCost) : pairIncrement z =
    ∫⁻ x : EvenState × OddState,
      ENNReal.ofReal (cost x.1.1) + ENNReal.ofReal (cost x.2.1) ∂pairedDraws z.1 := by
  rw [pairIncrement, pairVisits, add_apply, lintegral_add_measure,
    evenVisit, sampling_map_measure _ evenVisitMap_measurable,
    oddVisit, sampling_map_measure _ oddVisitMap_measurable,
    lintegral_map (g := fun x : EvenState × OddState ↦ evenVisitMap (z, x))
      increment_test_measurable (evenVisitMap_measurable.comp measurable_prodMk_left),
    lintegral_map (g := fun x : EvenState × OddState ↦ oddVisitMap (z, x))
      increment_test_measurable (oddVisitMap_measurable.comp measurable_prodMk_left)]
  change (∫⁻ x : EvenState × OddState, ENNReal.ofReal (cost x.1.1) ∂pairedDraws z.1) +
    (∫⁻ x : EvenState × OddState, ENNReal.ofReal (cost x.2.1) ∂pairedDraws z.1) = _
  exact (lintegral_add_left even_increment_measurable _).symm

theorem paired_age_balance (z : OddCost) (hz : 0 ≤ z.2) :
    (∫⁻ y : OddCost, ENNReal.ofReal y.2 ∂pairedCostKernel z) = ENNReal.ofReal z.2 + pairIncrement z := by
  have hK : pairedCostKernel = pairSampling.map pairUpdate := rfl
  rw [hK, sampling_map_measure _ pairUpdate_measurable,
    lintegral_map (g := fun x : EvenState × OddState ↦ pairUpdate (z, x)) age_test_measurable
      (pairUpdate_measurable.comp measurable_prodMk_left)]
  change (∫⁻ x : EvenState × OddState, ENNReal.ofReal (z.2 + cost x.1.1 + cost x.2.1) ∂pairedDraws z.1) = _
  have hp (x : EvenState × OddState) :
      ENNReal.ofReal (z.2 + cost x.1.1 + cost x.2.1) =
        ENNReal.ofReal z.2 + (ENNReal.ofReal (cost x.1.1) + ENNReal.ofReal (cost x.2.1)) := by
    have he : 0 ≤ cost x.1.1 := (cost_pos (by linarith [x.1.2])).le
    have ho : 0 ≤ cost x.2.1 := (cost_pos (by linarith [x.2.2])).le
    rw [ENNReal.ofReal_add (add_nonneg hz he) ho, ENNReal.ofReal_add hz he, add_assoc]
  simp_rw [hp]
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one, pairIncrement_formula]

theorem captured_killed_age_balance (z : OddCost) (hz : 0 ≤ z.2) :
    (∫⁻ y : OddCost, ENNReal.ofReal y.2 ∂costCaptured z) +
      (∫⁻ y : OddCost, ENNReal.ofReal y.2 ∂costKilled z) = ENNReal.ofReal z.2 + pairIncrement z := by
  rw [← lintegral_add_measure]
  have h := congrArg (fun K : Kernel OddCost OddCost ↦ K z) costCaptured_add_costKilled
  rw [add_apply] at h
  rw [h]
  exact paired_age_balance z hz

end Erdos970Dependency.OnePairCost

end

end Erdos970

end OAI
