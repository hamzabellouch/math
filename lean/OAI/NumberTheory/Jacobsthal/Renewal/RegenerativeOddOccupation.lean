import OAI.NumberTheory.Jacobsthal.Estimates.PairedBlockContraction
import OAI.NumberTheory.Jacobsthal.Estimates.RegenerativeResolvent
import OAI.NumberTheory.Jacobsthal.Probability.StateKernelInvariance

namespace OAI

namespace Erdos970

section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace Erdos970Dependency.RegenerationMass
open NumberTheoryLean.TransitionKernels NumberTheoryLean.PairedHitting
open Erdos970Dependency.InvariantDensities Erdos970Dependency.InvariantFiniteness
open Erdos970Dependency.OrdinaryKernelInvariance Erdos970Dependency.StateKernelInvariance

theorem oddMeasure_below_one : oddMeasure (Iio (1 : ℝ)) = 0 := by
  rw [oddMeasure, withDensity_apply _ measurableSet_Iio]
  apply setLIntegral_eq_zero measurableSet_Iio
  intro s hs
  change ENNReal.ofReal (InvariantDensities.oddDensity s) = 0
  unfold InvariantDensities.oddDensity
  rw [indicator_of_notMem (show s ∉ Ici (1 : ℝ) by change s < 1 at hs; change ¬1 ≤ s; linarith), ENNReal.ofReal_zero]

theorem oddMeasure_regeneration_interval : oddMeasure (Icc (1 : ℝ) 3) = ENNReal.ofReal beta := by
  rw [oddMeasure, withDensity_apply _ measurableSet_Icc,
    ← ofReal_integral_eq_lintegral_ofReal InvariantFiniteness.oddDensity_integrable.integrableOn
      (Filter.Eventually.of_forall InvariantDensities.oddDensity_nonneg)]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 3)]
  rfl

theorem oddMeasure_Iic_three : oddMeasure (Iic (3 : ℝ)) = ENNReal.ofReal beta := by
  rw [← Iio_union_Icc_eq_Iic (by norm_num : (1 : ℝ) ≤ 3)]
  rw [measure_union (by
    apply Set.disjoint_left.mpr
    intro s hs hcc
    exact (not_le_of_gt hs) hcc.1) measurableSet_Icc,
    oddMeasure_below_one, oddMeasure_regeneration_interval, zero_add]

theorem oddStateMeasure_regeneration : oddStateMeasure pairedRegeneration = ENNReal.ofReal beta := by
  rw [oddStateMeasure, Measure.map_apply oddLift_measurable pairedRegeneration_measurable]
  have hpre : oddLift ⁻¹' pairedRegeneration = Iic (3 : ℝ) := by
    ext s
    change max (95 / 100 : ℝ) s ≤ 3 ↔ s ≤ 3
    rw [max_le_iff]
    norm_num
  rw [hpre, oddMeasure_Iic_three]

theorem oddStateMeasure_mass_pos : 0 < oddStateMeasure univ := by
  have hpos : 0 < oddStateMeasure pairedRegeneration := by
    rw [oddStateMeasure_regeneration]
    exact ENNReal.ofReal_pos.mpr beta_pos
  exact hpos.trans_le (measure_mono (subset_univ _))

theorem stateMeasure_mass_pos : 0 < stateMeasure univ := by
  rw [stateMeasure, Measure.add_apply,
    Measure.map_apply measurable_inl MeasurableSet.univ,
    Measure.map_apply measurable_inr MeasurableSet.univ]
  simp only [preimage_univ]
  exact lt_of_lt_of_le oddStateMeasure_mass_pos (le_add_left le_rfl)

theorem stateMeasure_ne_zero : stateMeasure ≠ 0 := by
  intro h
  have hp := stateMeasure_mass_pos
  rw [h, Measure.coe_zero, Pi.zero_apply] at hp
  exact (lt_irrefl (0 : ℝ≥0∞)) hp

end Erdos970Dependency.RegenerationMass

end

section

open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory Topology
namespace Erdos970Dependency.RegenerativeOddOccupation
open NumberTheoryLean.TransitionKernels NumberTheoryLean.FinitePathMeasures
open NumberTheoryLean.PairedHitting NumberTheoryLean.PairedBlockContraction
open NumberTheoryLean.RegenerationTails NumberTheoryLean.KernelPotential
open Erdos970Dependency.InvariantDensities Erdos970Dependency.StateKernelInvariance
open Erdos970Dependency.RegenerationMass Erdos970Dependency.RegenerativeResolvent

theorem paired_invariance : pairedOdd ∘ₘ oddStateMeasure = oddStateMeasure := by
  rw [pairedOdd, ← Measure.comp_assoc, odd_state_invariance, even_state_invariance]

theorem odd_draw_common {s : OddState} (hs : s ∈ pairedRegeneration) :
    oddToEven s = oddToEven regenerationState := by
  rw [oddToEven, Kernel.comapRight_apply, Kernel.comapRight_apply,
    oddKernel_regeneration s hs]

theorem paired_common {s : OddState} (hs : s ∈ pairedRegeneration) :
    pairedOdd s = pairedOdd regenerationState := by
  rw [pairedOdd, Kernel.comp_apply, Kernel.comp_apply, odd_draw_common hs]

theorem killed_common {s : OddState} (hs : s ∈ pairedRegeneration) :
    pairedKilled s = pairedKilled regenerationState := by
  rw [pairedKilled, Kernel.restrict_apply, Kernel.restrict_apply, paired_common hs]

theorem odd_source_equation : oddStateMeasure = oddStateMeasure.restrict pairedRegeneration +
    pairedKilled ∘ₘ oddStateMeasure := by
  rw [pairedKilled, restrict_kernel_comp, paired_invariance]
  exact (Measure.restrict_add_restrict_compl pairedRegeneration_measurable).symm

noncomputable def ratioVisits : Kernel OddState State :=
  oddToEven.map Sum.inl + pairedOdd.map Sum.inr

instance ratioVisits_isFiniteKernel : IsFiniteKernel ratioVisits := by unfold ratioVisits; infer_instance

theorem ratioVisits_common {s : OddState} (hs : s ∈ pairedRegeneration) :
    ratioVisits s = ratioVisits regenerationState := by
  simp only [ratioVisits, add_apply, Kernel.map_apply _ measurable_inl, Kernel.map_apply _ measurable_inr]
  rw [odd_draw_common hs, paired_common hs]

theorem ratioVisits_invariant_mass : ratioVisits ∘ₘ oddStateMeasure = stateMeasure := by
  rw [ratioVisits, Measure.add_comp, ← Measure.map_comp _ _ measurable_inl,
    ← Measure.map_comp _ _ measurable_inr, odd_state_invariance, paired_invariance]
  rfl

noncomputable def ratioOccupation : Measure State :=
  potential ratioVisits pairedKilled regenerationState

theorem stateMeasure_eq_occupation : stateMeasure = ENNReal.ofReal beta • ratioOccupation := by
  have h := post_resolvent ratioVisits pairedKilled oddStateMeasure pairedRegeneration
    pairedRegeneration_measurable regenerationState odd_source_equation
    paired_survival_le_one paired_survival_tendsto_zero
    (fun _ hs ↦ ratioVisits_common hs) (fun _ hs ↦ killed_common hs)
  rw [ratioVisits_invariant_mass, oddStateMeasure_regeneration] at h
  exact h

theorem ratioOccupation_eq : ratioOccupation = (ENNReal.ofReal beta)⁻¹ • stateMeasure := by
  have h := congrArg (fun mu : Measure State ↦ (ENNReal.ofReal beta)⁻¹ • mu) stateMeasure_eq_occupation
  rw [smul_smul, ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr beta_pos))
    ENNReal.ofReal_ne_top, one_smul] at h
  exact h.symm

end Erdos970Dependency.RegenerativeOddOccupation

end

end Erdos970

end OAI
