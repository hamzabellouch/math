import OAI.NumberTheory.Jacobsthal.Renewal.RegenerationBandBounds

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.CostPrefixTransport

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostGrouping
open OccupationBoundaries CycleCostMoments OccupationDecomposition OccupationRegeneration
open InitialOccupation FullOccupationCovariance KernelPotential

instance costKernel_pow_markov (n : ℕ) : IsMarkovKernel (costKernel ^ n) := by
  induction n with
  | zero => change IsMarkovKernel (Kernel.id : Kernel CostState CostState); infer_instance
  | succ n ih =>
    have hp : costKernel ^ (n + 1) = costKernel ∘ₖ (costKernel ^ n) := pow_succ' _ _
    rw [hp]
    infer_instance

noncomputable def stateProjection : Kernel CostState State := Kernel.deterministic Prod.fst measurable_fst

theorem projection_intertwines : stateProjection ∘ₖ costKernel = stateKernel ∘ₖ stateProjection := by
  rw [stateProjection, Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap]
  ext z : 1
  rw [Kernel.map_apply _ measurable_fst, Kernel.comap_apply]
  exact Erdos970Dependency.ActualCycleOccupation.costKernel_map_state z

theorem projection_intertwines_pow (n : ℕ) :
    stateProjection ∘ₖ (costKernel ^ n) = (stateKernel ^ n) ∘ₖ stateProjection := by
  induction n with
  | zero =>
    change stateProjection ∘ₖ (Kernel.id : Kernel CostState CostState) = Kernel.id ∘ₖ stateProjection
    rw [Kernel.comp_id, Kernel.id_comp]
  | succ n ih =>
    have hp : costKernel ^ (n + 1) = (costKernel ^ n) ∘ₖ costKernel := pow_succ _ _
    have hq : stateKernel ^ (n + 1) = (stateKernel ^ n) ∘ₖ stateKernel := pow_succ _ _
    rw [hp, hq, ← Kernel.comp_assoc, ih, Kernel.comp_assoc, projection_intertwines, ← Kernel.comp_assoc]

theorem costKernel_pow_map_state (n : ℕ) (z : CostState) :
    ((costKernel ^ n) z).map Prod.fst = (stateKernel ^ n) z.1 := by
  have h := projection_intertwines_pow n
  rw [stateProjection, Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap] at h
  have hz := congrArg (fun K : Kernel CostState State => K z) h
  rwa [Kernel.map_apply _ measurable_fst, Kernel.comap_apply] at hz

theorem stateRatio_ge_half (s : State) : (1 / 2 : ℝ) ≤ stateRatio s := by
  cases s with
  | inl s => change (1 / 2 : ℝ) ≤ s.1; linarith [s.2]
  | inr s => change (1 / 2 : ℝ) ≤ s.1; linarith [s.2]

theorem costKernel_cost_bounds (z : CostState) :
    ∀ᵐ y ∂costKernel z, z.2 ≤ y.2 ∧ y.2 ≤ z.2 + Real.log 3 := by
  have hm : Measurable (fun s : State => (s, z.2 + cost (stateRatio s))) :=
    measurable_id.prodMk (measurable_const.add (cost_measurable.comp stateRatio_measurable))
  rw [costKernel_eq_map]
  apply (ae_map_iff hm.aemeasurable
    ((measurableSet_le measurable_const measurable_snd).inter (measurableSet_le measurable_snd measurable_const))).mpr
  apply Eventually.of_forall
  intro s
  have hp := cost_pos (stateRatio_pos s)
  have hu := draw_cost_le_log_three (stateRatio_ge_half s)
  change z.2 ≤ z.2 + cost (stateRatio s) ∧ z.2 + cost (stateRatio s) ≤ z.2 + Real.log 3
  constructor <;> linarith

theorem costKernel_pow_cost_bounds (n : ℕ) (z : CostState) :
    ∀ᵐ y ∂(costKernel ^ n) z, z.2 ≤ y.2 ∧ y.2 ≤ z.2 + (n : ℝ) * Real.log 3 := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero]
    change ∀ᵐ y ∂Measure.dirac z, z.2 ≤ y.2 ∧ y.2 ≤ z.2 + (0 : ℝ) * Real.log 3
    have hpred : MeasurableSet {y : CostState | z.2 ≤ y.2 ∧ y.2 ≤ z.2 + (0 : ℝ) * Real.log 3} :=
      (measurableSet_le measurable_const measurable_snd).inter (measurableSet_le measurable_snd measurable_const)
    exact (ae_dirac_iff (p := fun y : CostState => z.2 ≤ y.2 ∧ y.2 ≤ z.2 + (0 : ℝ) * Real.log 3) hpred).mpr
      ⟨le_rfl, by simp⟩
  | succ n ih =>
    have hp : costKernel ^ (n + 1) = costKernel ∘ₖ (costKernel ^ n) := pow_succ' _ _
    rw [hp]
    apply Kernel.ae_comp_of_ae_ae
      ((measurableSet_le measurable_const measurable_snd).inter (measurableSet_le measurable_snd measurable_const))
    filter_upwards [ih] with y hy
    filter_upwards [costKernel_cost_bounds y] with w hw
    refine ⟨le_trans hy.1 hw.1, ?_⟩
    calc
      w.2 ≤ y.2 + Real.log 3 := hw.2
      _ ≤ (z.2 + (n : ℝ) * Real.log 3) + Real.log 3 := add_le_add hy.2 le_rfl
      _ = _ := by push_cast; ring

noncomputable def inclusiveOccupation : Kernel CostState CostState := Kernel.id + fullOccupation

instance inclusiveOccupation_isSFiniteKernel : IsSFiniteKernel inclusiveOccupation := by
  unfold inclusiveOccupation
  infer_instance

theorem inclusiveOccupation_translation (z : CostState) (a : ℝ) :
    (inclusiveOccupation z).map (shiftFullCost a) = inclusiveOccupation (shiftFullCost a z) := by
  rw [inclusiveOccupation, _root_.add_apply, Measure.map_add _ _ (shiftFullCost_measurable a),
    Kernel.id_apply, Measure.map_dirac' (shiftFullCost_measurable a), fullOccupation_translation,
    _root_.add_apply, Kernel.id_apply]

theorem inclusive_comp_step : inclusiveOccupation ∘ₖ costKernel = fullOccupation := by
  rw [inclusiveOccupation, Kernel.comp_add_left, Kernel.id_comp]
  exact fullOccupation_unfold.symm

noncomputable def prefixOccupation (n : ℕ) : Kernel CostState CostState := inclusiveOccupation ∘ₖ (costKernel ^ n)

instance prefixOccupation_isSFiniteKernel (n : ℕ) : IsSFiniteKernel (prefixOccupation n) := by
  unfold prefixOccupation
  infer_instance

theorem full_comp_step_le : fullOccupation ∘ₖ costKernel ≤ fullOccupation := by
  calc
    _ ≤ costKernel + fullOccupation ∘ₖ costKernel := le_add_of_nonneg_left bot_le
    _ = _ := fullOccupation_unfold.symm

theorem full_comp_pow_le (n : ℕ) : fullOccupation ∘ₖ (costKernel ^ n) ≤ fullOccupation := by
  induction n with
  | zero => change fullOccupation ∘ₖ Kernel.id ≤ fullOccupation; rw [Kernel.comp_id]
  | succ n ih =>
    have hp : costKernel ^ (n + 1) = (costKernel ^ n) ∘ₖ costKernel := pow_succ _ _
    rw [hp, ← Kernel.comp_assoc]
    exact le_trans (compose_mono_left ih costKernel) full_comp_step_le

theorem prefixOccupation_le_full (n : ℕ) (hn : 0 < n) : prefixOccupation n ≤ fullOccupation := by
  cases n with
  | zero => omega
  | succ n =>
    have hp : costKernel ^ (n + 1) = costKernel ∘ₖ (costKernel ^ n) := pow_succ' _ _
    rw [prefixOccupation, hp, ← Kernel.comp_assoc, inclusive_comp_step]
    exact full_comp_pow_le n

end NumberTheoryLean.CostPrefixTransport

end

end Erdos970

end OAI
