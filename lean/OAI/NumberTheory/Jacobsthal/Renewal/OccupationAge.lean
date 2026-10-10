import AbsorptionCutoff.Supercritical.RenewalApprox
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Kernel.Composition.CompMap
import Mathlib.Probability.Moments.IntegrableExpMul
import OAI.NumberTheory.Jacobsthal.Estimates.MinorizingCostRegularity
import OAI.NumberTheory.Jacobsthal.Estimates.PairedCostGrouping
import OAI.NumberTheory.Jacobsthal.Renewal.RegenerativeOddOccupation

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.CycleCostAtomless

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures KernelDensityBridge
open PairedCostProcess CostReturnLaw MinorizingCostRegularity

theorem positive_second_cost_level_null (T y : ℝ) :
    ((volume : Measure ℝ).prod volume) {x : ℝ × ℝ | 0 < x.2 ∧ T + cost x.1 + cost x.2 = y} = 0 := by
  have hA : MeasurableSet {x : ℝ × ℝ | 0 < x.2 ∧ T + cost x.1 + cost x.2 = y} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_eq_fun ((measurable_const.add (cost_measurable.comp measurable_fst)).add
        (cost_measurable.comp measurable_snd)) measurable_const)
  rw [Measure.prod_apply hA]
  apply lintegral_eq_zero_of_ae_eq_zero
  apply Eventually.of_forall
  intro t
  apply Set.Subsingleton.measure_zero
  intro u hu v hv
  have hu0 : 0 < u := hu.1
  have hv0 : 0 < v := hv.1
  have huEq : T + cost t + cost u = y := hu.2
  have hvEq : T + cost t + cost v = y := hv.2
  exact cost_strictAntiOn.injOn hu0 hv0 (by linarith)

theorem oddTwoStep_second_positive (s : OddState) : ∀ᵐ x ∂oddTwoStep s, 0 < x.2 := by
  have hm : Measurable (fun x : EvenState × OddState => (x.1.1, x.2.1)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk (measurable_subtype_coe.comp measurable_snd)
  rw [oddTwoStep, Kernel.map_apply _ hm]
  apply (ae_map_iff hm.aemeasurable (measurableSet_lt measurable_const measurable_snd)).mpr
  exact Eventually.of_forall (fun x => by change 0 < x.2.1; linarith [x.2.2])

theorem oddTwoStep_cost_level (s : OddState) (T y : ℝ) :
    oddTwoStep s {x : ℝ × ℝ | T + cost x.1 + cost x.2 = y} = 0 := by
  have heq : {x : ℝ × ℝ | T + cost x.1 + cost x.2 = y} =ᵐ[oddTwoStep s]
      {x : ℝ × ℝ | 0 < x.2 ∧ T + cost x.1 + cost x.2 = y} := by
    filter_upwards [oddTwoStep_second_positive s] with x hx
    exact propext ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩
  rw [measure_congr heq, oddTwoStep_eq_withDensity]
  exact withDensity_absolutelyContinuous _ _ (positive_second_cost_level_null T y)

theorem pairedCost_cost_level (z : OddCost) (y : ℝ) :
    pairedCostKernel z {w : OddCost | w.2 = y} = 0 := by
  have hm : Measurable (fun x : EvenState × OddState => (x.1.1, x.2.1)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk (measurable_subtype_coe.comp measurable_snd)
  have hB : MeasurableSet {x : ℝ × ℝ | z.2 + cost x.1 + cost x.2 = y} :=
    measurableSet_eq_fun ((measurable_const.add (cost_measurable.comp measurable_fst)).add
      (cost_measurable.comp measurable_snd)) measurable_const
  have h := oddTwoStep_cost_level z.1 z.2 y
  rw [oddTwoStep, Kernel.map_apply _ hm, Measure.map_apply hm hB] at h
  rw [pairedCostKernel_apply z (measurableSet_eq_fun measurable_snd measurable_const)]
  exact h

theorem captured_cost_level (z : OddCost) (y : ℝ) : costCaptured z {w : OddCost | w.2 = y} = 0 := by
  rw [costCaptured, Kernel.restrict_apply' _ _ _ (measurableSet_eq_fun measurable_snd measurable_const)]
  exact measure_mono_null inter_subset_left (pairedCost_cost_level z y)

theorem firstReturn_cost_level (n : ℕ) (z : OddCost) (y : ℝ) :
    firstReturn n z {w : OddCost | w.2 = y} = 0 := by
  rw [firstReturn, Kernel.comp_apply' _ _ _ (measurableSet_eq_fun measurable_snd measurable_const)]
  simp only [captured_cost_level, lintegral_zero]

theorem returnLaw_cost_level (z : OddCost) (y : ℝ) : returnLaw z {w : OddCost | w.2 = y} = 0 := by
  rw [returnLaw, Kernel.sum_apply' _ _ (measurableSet_eq_fun measurable_snd measurable_const)]
  simp only [firstReturn_cost_level, tsum_zero]

instance cycleCostLaw_nullSingletonClass : NullSingletonClass cycleCostLaw := by
  constructor
  intro y
  rw [cycleCostLaw, Measure.map_apply measurable_snd (measurableSet_singleton y)]
  exact returnLaw_cost_level (RegenerationTails.regenerationState, 0) y

theorem cycleCostLaw_countable_null {C : Set ℝ} (hC : C.Countable) : cycleCostLaw C = 0 :=
  hC.measure_zero _

theorem cycleCostLaw_lattice_null (a r : ℝ) :
    cycleCostLaw {x : ℝ | ∃ k : ℤ, x = a + k * r} = 0 := by
  apply cycleCostLaw_countable_null
  apply (countable_range (fun k : ℤ => a + k * r)).mono
  intro x hx
  obtain ⟨k, hk⟩ := hx
  exact ⟨k, hk.symm⟩

end NumberTheoryLean.CycleCostAtomless

end

section

namespace NumberTheoryLean.CycleCostLower

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostProcess CostReturnLaw
open MinorizingCostRegularity

theorem pairedCost_cost_monotone (z : OddCost) : ∀ᵐ y ∂pairedCostKernel z, z.2 ≤ y.2 := by
  apply ae_iff.mpr
  simp only [not_le]
  change pairedCostKernel z {y : OddCost | y.2 < z.2} = 0
  rw [pairedCostKernel_apply z (measurableSet_lt measurable_snd measurable_const)]
  have he : {x : EvenState × OddState | (x.2, z.2 + cost x.1.1 + cost x.2.1) ∈ {y : OddCost | y.2 < z.2}} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have h1 : 0 < cost x.1.1 := cost_pos (by linarith [x.1.2])
    have h2 : 0 < cost x.2.1 := cost_pos (by linarith [x.2.2])
    change z.2 + cost x.1.1 + cost x.2.1 < z.2 at hx
    linarith
  rw [he, measure_empty]

theorem costKilled_cost_monotone (z : OddCost) : ∀ᵐ y ∂costKilled z, z.2 ≤ y.2 :=
  ae_restrict_of_ae (pairedCost_cost_monotone z)

theorem costKilled_pow_cost_monotone (n : ℕ) (z : OddCost) :
    ∀ᵐ y ∂(costKilled ^ n) z, z.2 ≤ y.2 := by
  induction n generalizing z with
  | zero =>
    change ∀ᵐ y ∂Measure.dirac z, z.2 ≤ y.2
    exact (ae_dirac_iff (measurableSet_le measurable_const measurable_snd)).mpr le_rfl
  | succ n ih =>
    have hp : costKilled ^ (n + 1) = costKilled ∘ₖ (costKilled ^ n) := pow_succ' costKilled n
    rw [hp]
    apply Kernel.ae_comp_of_ae_ae (measurableSet_le measurable_const measurable_snd)
    filter_upwards [ih z] with y hy
    filter_upwards [costKilled_cost_monotone y] with w hw
    exact le_trans hy hw

theorem captured_cost_lower (z : OddCost) :
    ∀ᵐ y ∂costCaptured z, z.2 + cost 3 ≤ y.2 := by
  apply ae_iff.mpr
  simp only [not_le]
  change costCaptured z {y : OddCost | y.2 < z.2 + cost 3} = 0
  have hB : MeasurableSet {y : OddCost | y.2 < z.2 + cost 3} :=
    measurableSet_lt measurable_snd measurable_const
  rw [costCaptured, Kernel.restrict_apply' _ _ _ hB,
    pairedCostKernel_apply z (hB.inter returnSet_measurable)]
  have he : {x : EvenState × OddState | (x.2, z.2 + cost x.1.1 + cost x.2.1) ∈
      ({y : OddCost | y.2 < z.2 + cost 3} ∩ returnSet)} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hu : x.2.1 ≤ 3 := hx.2
    have hcost : cost 3 ≤ cost x.2.1 := cost_strictAntiOn.antitoneOn
      (by change 0 < x.2.1; linarith [x.2.2]) (by norm_num) hu
    have hfirst : 0 < cost x.1.1 := cost_pos (by linarith [x.1.2])
    have hbad : z.2 + cost x.1.1 + cost x.2.1 < z.2 + cost 3 := hx.1
    linarith
  rw [he, measure_empty]

theorem firstReturn_cost_lower (n : ℕ) (z : OddCost) :
    ∀ᵐ y ∂firstReturn n z, z.2 + cost 3 ≤ y.2 := by
  rw [firstReturn]
  apply Kernel.ae_comp_of_ae_ae (measurableSet_le measurable_const measurable_snd)
  filter_upwards [costKilled_pow_cost_monotone n z] with y hy
  filter_upwards [captured_cost_lower y] with w hw
  linarith

theorem returnLaw_cost_lower (z : OddCost) : ∀ᵐ y ∂returnLaw z, z.2 + cost 3 ≤ y.2 := by
  rw [returnLaw, Kernel.sum_apply, Measure.ae_sum_iff]
  exact fun n => firstReturn_cost_lower n z

theorem cost_three : cost 3 = Real.log (4 / 3) := by
  unfold cost
  congr 1
  norm_num

theorem cycleCostLaw_lower : ∀ᵐ G ∂cycleCostLaw, Real.log (4 / 3) ≤ G := by
  change ∀ᵐ G ∂(returnLaw (RegenerationTails.regenerationState, 0)).map Prod.snd, Real.log (4 / 3) ≤ G
  apply (ae_map_iff measurable_snd.aemeasurable measurableSet_Ici).mpr
  have h := returnLaw_cost_lower (RegenerationTails.regenerationState, 0)
  simpa only [zero_add, cost_three] using h

theorem cycleCostLaw_positive : ∀ᵐ G ∂cycleCostLaw, 0 < G := by
  filter_upwards [cycleCostLaw_lower] with G hG
  exact lt_of_lt_of_le (by rw [← cost_three]; exact cost_pos (by norm_num)) hG

end NumberTheoryLean.CycleCostLower

end

section

namespace NumberTheoryLean.CycleRegeneration

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels PairedCostProcess CostReturnLaw RegenerationTails

theorem costKilled_regeneration (s : OddState) (hs : s.1 ≤ 3) (T : ℝ) :
    costKilled (s, T) = costKilled (regenerationState, T) := by
  rw [costKilled, Kernel.restrict_apply, Kernel.restrict_apply, pairedCost_regeneration s hs T]

theorem costCaptured_regeneration (s : OddState) (hs : s.1 ≤ 3) (T : ℝ) :
    costCaptured (s, T) = costCaptured (regenerationState, T) := by
  rw [costCaptured, Kernel.restrict_apply, Kernel.restrict_apply, pairedCost_regeneration s hs T]

theorem firstReturn_regeneration (n : ℕ) (s : OddState) (hs : s.1 ≤ 3) (T : ℝ) :
    firstReturn n (s, T) = firstReturn n (regenerationState, T) := by
  cases n with
  | zero =>
    change (costCaptured ∘ₖ (Kernel.id : Kernel OddCost OddCost)) (s, T) =
      (costCaptured ∘ₖ (Kernel.id : Kernel OddCost OddCost)) (regenerationState, T)
    rw [Kernel.comp_id]
    exact costCaptured_regeneration s hs T
  | succ n =>
    have hp : costKilled ^ (n + 1) = (costKilled ^ n) ∘ₖ costKilled := pow_succ costKilled n
    have hq : (costKilled ^ (n + 1)) (s, T) = (costKilled ^ (n + 1)) (regenerationState, T) := by
      rw [hp, Kernel.comp_apply, Kernel.comp_apply, costKilled_regeneration s hs T]
    rw [firstReturn, Kernel.comp_apply, Kernel.comp_apply, hq]

theorem returnLaw_regeneration (s : OddState) (hs : s.1 ≤ 3) (T : ℝ) :
    returnLaw (s, T) = returnLaw (regenerationState, T) := by
  ext B hB
  rw [returnLaw, Kernel.sum_apply' _ _ hB, Kernel.sum_apply' _ _ hB]
  apply tsum_congr
  intro n
  rw [firstReturn_regeneration n s hs T]

theorem costKilled_translation (z : OddCost) (a : ℝ) :
    (costKilled z).map (shiftCost a) = costKilled (shiftCost a z) := by
  rw [costKilled, Kernel.restrict_apply, Kernel.restrict_apply]
  calc
    _ = ((pairedCostKernel z).map (shiftCost a)).restrict returnSetᶜ :=
      (Measure.restrict_map (shiftCost_measurable a) returnSet_measurable.compl).symm
    _ = _ := by rw [pairedCost_translation]; rfl

theorem costCaptured_translation (z : OddCost) (a : ℝ) :
    (costCaptured z).map (shiftCost a) = costCaptured (shiftCost a z) := by
  rw [costCaptured, Kernel.restrict_apply, Kernel.restrict_apply]
  calc
    _ = ((pairedCostKernel z).map (shiftCost a)).restrict returnSet :=
      (Measure.restrict_map (shiftCost_measurable a) returnSet_measurable).symm
    _ = _ := by rw [pairedCost_translation]; rfl

noncomputable def shiftKernel (a : ℝ) : Kernel OddCost OddCost :=
  Kernel.deterministic (shiftCost a) (shiftCost_measurable a)

theorem shift_commutes_killed (a : ℝ) : Commute (shiftKernel a) costKilled := by
  change shiftKernel a ∘ₖ costKilled = costKilled ∘ₖ shiftKernel a
  rw [shiftKernel, Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap]
  ext z : 1
  rw [Kernel.map_apply _ (shiftCost_measurable a), Kernel.comap_apply]
  exact costKilled_translation z a

theorem shift_commutes_captured (a : ℝ) : Commute (shiftKernel a) costCaptured := by
  change shiftKernel a ∘ₖ costCaptured = costCaptured ∘ₖ shiftKernel a
  rw [shiftKernel, Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap]
  ext z : 1
  rw [Kernel.map_apply _ (shiftCost_measurable a), Kernel.comap_apply]
  exact costCaptured_translation z a

theorem shift_commutes_firstReturn (a : ℝ) (n : ℕ) : Commute (shiftKernel a) (firstReturn n) :=
  (shift_commutes_captured a).mul_right ((shift_commutes_killed a).pow_right n)

theorem shift_commutes_returnLaw (a : ℝ) : Commute (shiftKernel a) returnLaw := by
  change shiftKernel a ∘ₖ returnLaw = returnLaw ∘ₖ shiftKernel a
  rw [returnLaw, Kernel.comp_sum_right, Kernel.comp_sum_left]
  apply congrArg Kernel.sum
  funext n
  exact (shift_commutes_firstReturn a n).eq

theorem returnLaw_translation (z : OddCost) (a : ℝ) :
    (returnLaw z).map (shiftCost a) = returnLaw (shiftCost a z) := by
  have h := (shift_commutes_returnLaw a).eq
  change shiftKernel a ∘ₖ returnLaw = returnLaw ∘ₖ shiftKernel a at h
  rw [shiftKernel, Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap] at h
  have hz := congrArg (fun K : Kernel OddCost OddCost => K z) h
  rwa [Kernel.map_apply _ (shiftCost_measurable a), Kernel.comap_apply] at hz

noncomputable def cycleJointLaw : Measure OddCost := returnLaw (regenerationState, 0)

instance cycleJointLaw_isProbabilityMeasure : IsProbabilityMeasure cycleJointLaw := by
  unfold cycleJointLaw
  infer_instance

theorem return_increment_law (s : OddState) (hs : s.1 ≤ 3) (T : ℝ) :
    (returnLaw (s, T)).map (shiftCost (-T)) = cycleJointLaw := by
  rw [returnLaw_regeneration s hs T]
  have ht := returnLaw_translation (regenerationState, 0) T
  have hz : shiftCost T (regenerationState, 0) = (regenerationState, T) := by simp [shiftCost]
  rw [hz] at ht
  rw [← ht, Measure.map_map (shiftCost_measurable (-T)) (shiftCost_measurable T)]
  have heq : shiftCost (-T) ∘ shiftCost T = id := by
    funext z
    ext <;> simp [shiftCost, Function.comp_apply, add_assoc]
  rw [heq, Measure.map_id]
  rfl

theorem returnLaw_ae_regeneration (z : OddCost) : ∀ᵐ y ∂returnLaw z, y ∈ returnSet := by
  apply ae_iff.mpr
  exact returnLaw_off_returnSet z

theorem cycle_increment_integral (z : OddCost) (hz : z ∈ returnSet)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y, F (y.2 - z.2) ∂returnLaw z) = ∫⁻ G, F G ∂cycleCostLaw := by
  have h := congrArg (fun μ : Measure OddCost => ∫⁻ y, F y.2 ∂μ) (return_increment_law z.1 hz z.2)
  rw [lintegral_map (f := fun y : OddCost => F y.2) (hF.comp measurable_snd) (shiftCost_measurable (-z.2))] at h
  rw [cycleCostLaw, lintegral_map hF measurable_snd]
  simpa only [shiftCost, sub_eq_add_neg, cycleJointLaw] using h

noncomputable def cycleProductExpectation : List (ℝ → ℝ≥0∞) → OddCost → ℝ≥0∞
  | [], _ => 1
  | F :: Fs, z => ∫⁻ y, F (y.2 - z.2) * cycleProductExpectation Fs y ∂returnLaw z

theorem finite_cycle_cost_factorization (Fs : List (ℝ → ℝ≥0∞))
    (hFs : ∀ F ∈ Fs, Measurable F) (z : OddCost) (hz : z ∈ returnSet) :
    cycleProductExpectation Fs z = (Fs.map (fun F => ∫⁻ G, F G ∂cycleCostLaw)).prod := by
  induction Fs generalizing z with
  | nil => rfl
  | cons F Fs ih =>
    have hF : Measurable F := hFs F (by simp)
    have hrest : ∀ G ∈ Fs, Measurable G := fun G hG => hFs G (by simp [hG])
    change (∫⁻ y, F (y.2 - z.2) * cycleProductExpectation Fs y ∂returnLaw z) =
      (∫⁻ G, F G ∂cycleCostLaw) * (Fs.map (fun F => ∫⁻ G, F G ∂cycleCostLaw)).prod
    calc
      _ = ∫⁻ y, F (y.2 - z.2) * (Fs.map (fun F => ∫⁻ G, F G ∂cycleCostLaw)).prod ∂returnLaw z := by
        apply lintegral_congr_ae
        filter_upwards [returnLaw_ae_regeneration z] with y hy
        rw [ih hrest y hy]
      _ = (∫⁻ y, F (y.2 - z.2) ∂returnLaw z) * (Fs.map (fun F => ∫⁻ G, F G ∂cycleCostLaw)).prod :=
        lintegral_mul_const _ (hF.comp (measurable_snd.sub measurable_const))
      _ = _ := by rw [cycle_increment_integral z hz hF]

end NumberTheoryLean.CycleRegeneration

end

section

namespace NumberTheoryLean.MarkedCycleLaw

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open PairedCostProcess CostReturnLaw CycleRegeneration

abbrev MarkedReturn := ℕ × OddCost

def markReturn (n : ℕ) (z : OddCost) : MarkedReturn := (2 * (n + 1), z)

theorem markReturn_measurable (n : ℕ) : Measurable (markReturn n) :=
  measurable_const.prodMk measurable_id

noncomputable def firstMarkedReturn (n : ℕ) : Kernel OddCost MarkedReturn :=
  (firstReturn n).map (markReturn n)

instance firstMarkedReturn_isFiniteKernel (n : ℕ) : IsFiniteKernel (firstMarkedReturn n) := by
  unfold firstMarkedReturn
  infer_instance

noncomputable def markedReturnLaw : Kernel OddCost MarkedReturn := Kernel.sum firstMarkedReturn

instance markedReturnLaw_isMarkovKernel : IsMarkovKernel markedReturnLaw := by
  constructor
  intro z
  constructor
  rw [markedReturnLaw, Kernel.sum_apply' _ _ MeasurableSet.univ]
  have heq : ∀ n, firstMarkedReturn n z univ = firstReturn n z univ := by
    intro n
    rw [firstMarkedReturn, Kernel.map_apply' _ (markReturn_measurable n) _ MeasurableSet.univ, preimage_univ]
  simp_rw [heq]
  rw [← Kernel.sum_apply' firstReturn z MeasurableSet.univ]
  change returnLaw z univ = 1
  exact measure_univ

theorem markedReturnLaw_forget (z : OddCost) : (markedReturnLaw z).map Prod.snd = returnLaw z := by
  ext B hB
  rw [Measure.map_apply measurable_snd hB, markedReturnLaw,
    Kernel.sum_apply' _ _ (measurable_snd hB), returnLaw, Kernel.sum_apply' _ _ hB]
  apply tsum_congr
  intro n
  rw [firstMarkedReturn, Kernel.map_apply' _ (markReturn_measurable n) _ (measurable_snd hB)]
  rfl

theorem markedReturnLaw_duration_ge_two (z : OddCost) : ∀ᵐ x ∂markedReturnLaw z, 2 ≤ x.1 := by
  rw [markedReturnLaw, Kernel.sum_apply, Measure.ae_sum_iff]
  intro n
  rw [firstMarkedReturn, Kernel.map_apply _ (markReturn_measurable n)]
  apply (ae_map_iff (markReturn_measurable n).aemeasurable
    (measurableSet_le measurable_const measurable_fst)).mpr
  exact Eventually.of_forall (fun _ => by change 2 ≤ 2 * (n + 1); omega)

theorem markedReturnLaw_ae_regeneration (z : OddCost) :
    ∀ᵐ x ∂markedReturnLaw z, x.2 ∈ returnSet := by
  apply (ae_map_iff measurable_snd.aemeasurable returnSet_measurable).mp
  rw [markedReturnLaw_forget]
  exact returnLaw_ae_regeneration z

noncomputable def markedCycleLaw : Measure MarkedReturn :=
  markedReturnLaw (RegenerationTails.regenerationState, 0)

instance markedCycleLaw_isProbabilityMeasure : IsProbabilityMeasure markedCycleLaw := by
  unfold markedCycleLaw
  infer_instance

noncomputable def durationLaw : Measure ℕ := markedCycleLaw.map Prod.fst

instance durationLaw_isProbabilityMeasure : IsProbabilityMeasure durationLaw :=
  (Measure.isProbabilityMeasure_map_iff (μ := markedCycleLaw)
    measurable_fst.aemeasurable).mpr inferInstance

theorem durationLaw_ge_two : ∀ᵐ n ∂durationLaw, 2 ≤ n := by
  apply (ae_map_iff measurable_fst.aemeasurable measurableSet_Ici).mpr
  exact markedReturnLaw_duration_ge_two _

theorem durationLaw_positive : ∀ᵐ n ∂durationLaw, 0 < n := by
  filter_upwards [durationLaw_ge_two] with n hn
  omega

theorem markedCycleLaw_cost_projection :
    markedCycleLaw.map (fun x => x.2.2) = cycleCostLaw := by
  have h := markedReturnLaw_forget (RegenerationTails.regenerationState, 0)
  change markedCycleLaw.map Prod.snd = returnLaw (RegenerationTails.regenerationState, 0) at h
  rw [cycleCostLaw, ← h, Measure.map_map measurable_snd measurable_snd]
  rfl

theorem durationLaw_lintegral (H : ℕ → ℝ≥0∞) :
    (∫⁻ n, H n ∂durationLaw) = ∑' n : ℕ,
      H (2 * (n + 1)) * firstReturn n (RegenerationTails.regenerationState, 0) univ := by
  have hH : Measurable H := measurable_of_countable H
  rw [durationLaw, lintegral_map hH measurable_fst, markedCycleLaw,
    markedReturnLaw, Kernel.sum_apply, lintegral_sum_measure]
  apply tsum_congr
  intro n
  rw [firstMarkedReturn, Kernel.map_apply _ (markReturn_measurable n),
    lintegral_map (f := fun x : MarkedReturn => H x.1) (hH.comp measurable_fst) (markReturn_measurable n)]
  change (∫⁻ _z, H (2 * (n + 1)) ∂firstReturn n (RegenerationTails.regenerationState, 0)) = _
  rw [lintegral_const]

end NumberTheoryLean.MarkedCycleLaw

end

section

namespace NumberTheoryLean.CycleDurationMoments

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open TransitionKernels PairedHitting PairedDrift PairedBlockContraction PairedCostProcess
open CostReturnLaw MarkedCycleLaw

noncomputable def durationFrom (z : OddCost) : Measure ℕ := (markedReturnLaw z).map Prod.fst

instance durationFrom_isProbabilityMeasure (z : OddCost) : IsProbabilityMeasure (durationFrom z) :=
  (Measure.isProbabilityMeasure_map_iff (μ := markedReturnLaw z)
    measurable_fst.aemeasurable).mpr inferInstance

theorem durationFrom_lintegral (z : OddCost) (H : ℕ → ℝ≥0∞) :
    (∫⁻ n, H n ∂durationFrom z) = ∑' n : ℕ, H (2 * (n + 1)) * firstReturn n z univ := by
  have hH : Measurable H := measurable_of_countable H
  rw [durationFrom, lintegral_map hH measurable_fst, markedReturnLaw, Kernel.sum_apply, lintegral_sum_measure]
  apply tsum_congr
  intro n
  rw [firstMarkedReturn, Kernel.map_apply _ (markReturn_measurable n),
    lintegral_map (f := fun x : MarkedReturn => H x.1) (hH.comp measurable_fst) (markReturn_measurable n)]
  change (∫⁻ _y, H (2 * (n + 1)) ∂firstReturn n z) = _
  rw [lintegral_const]

theorem firstReturn_geometric : ∃ m : ℕ, 0 < m ∧ ∃ ρ D : ℝ, 0 < ρ ∧ ρ < 1 ∧ 0 < D ∧
    ∀ n : ℕ, ∀ z : OddCost, firstReturn n z univ ≤ ENNReal.ofReal (ρ ^ (n / m) * (V z.1 + D)) := by
  obtain ⟨m, hm, ρ, D, hρ, hρ1, hD, hb⟩ := paired_survival_geometric
  refine ⟨m, hm, ρ, D, hρ, hρ1, hD, ?_⟩
  intro n z
  calc
    _ ≤ firstReturn n z univ + (costKilled ^ (n + 1)) z univ := le_add_of_nonneg_right zero_le
    _ = (costKilled ^ n) z univ := return_mass_step n z
    _ = (pairedKilled ^ n) z.1 univ := costKilled_mass n z
    _ ≤ (pairedKilled ^ (m * (n / m))) z.1 univ := paired_survival_antitone z.1 (Nat.mul_div_le n m)
    _ ≤ _ := hb (n / m) z.1

theorem weighted_geometric_bound {m : ℕ} (hm : 0 < m) {ρ θ : ℝ}
    (hρ : 0 < ρ) (hθ : 0 < θ) (hrel : 4 * (m : ℝ) * θ = -Real.log ρ) (n : ℕ) :
    Real.exp (θ * (2 * ((n : ℝ) + 1))) * ρ ^ (n / m) ≤
      Real.exp (-Real.log ρ + 2 * θ) * (Real.exp (-2 * θ)) ^ n := by
  have hlog : Real.log ρ = -4 * (m : ℝ) * θ := by linarith
  have hmod : ((n % m : ℕ) : ℝ) < (m : ℝ) := by exact_mod_cast Nat.mod_lt n hm
  have hdiv : (n : ℝ) = (m : ℝ) * ((n / m : ℕ) : ℝ) + ((n % m : ℕ) : ℝ) := by
    have h : ((n % m : ℕ) : ℝ) + (m : ℝ) * ((n / m : ℕ) : ℝ) = (n : ℝ) := by
      exact_mod_cast Nat.mod_add_div n m
    linarith
  have he : θ * (2 * ((n : ℝ) + 1)) + ((n / m : ℕ) : ℝ) * Real.log ρ ≤
      (-Real.log ρ + 2 * θ) + (n : ℝ) * (-2 * θ) := by
    rw [hlog, hdiv]
    nlinarith [mul_nonneg hθ.le (sub_nonneg.mpr hmod.le)]
  calc
    _ = Real.exp (θ * (2 * ((n : ℝ) + 1)) + ((n / m : ℕ) : ℝ) * Real.log ρ) := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hρ]
    _ ≤ Real.exp ((-Real.log ρ + 2 * θ) + (n : ℝ) * (-2 * θ)) := Real.exp_le_exp.mpr he
    _ = _ := by rw [Real.exp_add, Real.exp_nat_mul]

theorem return_duration_exponential_moment : ∃ θ : ℝ, 0 < θ ∧ ∀ z : OddCost,
    (∫⁻ n, ENNReal.ofReal (Real.exp (θ * (n : ℝ))) ∂durationFrom z) < ∞ := by
  obtain ⟨m, hm, ρ, D, hρ, hρ1, hD, hb⟩ := firstReturn_geometric
  let θ := -Real.log ρ / (4 * (m : ℝ))
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hθ : 0 < θ := div_pos (neg_pos.mpr (Real.log_neg hρ hρ1)) (by positivity)
  have hrel : 4 * (m : ℝ) * θ = -Real.log ρ := by dsimp [θ]; field_simp
  refine ⟨θ, hθ, ?_⟩
  intro z
  let A := Real.exp (-Real.log ρ + 2 * θ) * (V z.1 + D)
  let r := Real.exp (-2 * θ)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hsum : Summable (fun n : ℕ => A * r ^ n) := (summable_geometric_of_lt_one hr0 hr1).mul_left A
  rw [durationFrom_lintegral]
  apply lt_of_le_of_lt (ENNReal.tsum_le_tsum ?_) hsum.tsum_ofReal_lt_top
  intro n
  have hW : 0 < V z.1 + D := add_pos (V_pos z.1) hD
  have hn := weighted_geometric_bound hm hρ hθ hrel n
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  calc
    _ ≤ ENNReal.ofReal (Real.exp (θ * (2 * ((n : ℝ) + 1)))) *
        ENNReal.ofReal (ρ ^ (n / m) * (V z.1 + D)) := mul_le_mul le_rfl (hb n z) zero_le zero_le
    _ = ENNReal.ofReal ((Real.exp (θ * (2 * ((n : ℝ) + 1)))) * ρ ^ (n / m) * (V z.1 + D)) := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (A * r ^ n) := ENNReal.ofReal_le_ofReal (by
      dsimp [A, r]
      nlinarith [mul_le_mul_of_nonneg_right hn hW.le])

theorem return_duration_exponential_integrable : ∃ θ : ℝ, 0 < θ ∧ ∀ z : OddCost,
    Integrable (fun n : ℕ => Real.exp (θ * (n : ℝ))) (durationFrom z) := by
  obtain ⟨θ, hθ, hb⟩ := return_duration_exponential_moment
  refine ⟨θ, hθ, ?_⟩
  intro z
  refine ⟨(measurable_of_countable _).aestronglyMeasurable, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun n : ℕ => (Real.exp_pos (θ * (n : ℝ))).le))).mpr (hb z)

theorem cycle_duration_exponential_integrable : ∃ θ : ℝ, 0 < θ ∧
    Integrable (fun n : ℕ => Real.exp (θ * (n : ℝ))) durationLaw := by
  obtain ⟨θ, hθ, hb⟩ := return_duration_exponential_integrable
  exact ⟨θ, hθ, hb (RegenerationTails.regenerationState, 0)⟩

end NumberTheoryLean.CycleDurationMoments

end

section

namespace NumberTheoryLean.CycleCostMoments

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostProcess CostReturnLaw
open MarkedCycleLaw CycleDurationMoments

theorem draw_cost_le_log_three {s : ℝ} (hs : 1 / 2 ≤ s) : cost s ≤ Real.log 3 := by
  have hs0 : 0 < s := by linarith
  have hi : 1 / s ≤ 2 := (div_le_iff₀ hs0).mpr (by linarith)
  unfold cost
  exact Real.log_le_log (by positivity) (by linarith)

theorem pairedCost_cost_upper (z : OddCost) :
    ∀ᵐ y ∂pairedCostKernel z, y.2 ≤ z.2 + 2 * Real.log 3 := by
  apply ae_iff.mpr
  simp only [not_le]
  change pairedCostKernel z {y : OddCost | z.2 + 2 * Real.log 3 < y.2} = 0
  rw [pairedCostKernel_apply z (measurableSet_lt measurable_const measurable_snd)]
  have he : {x : EvenState × OddState | (x.2, z.2 + cost x.1.1 + cost x.2.1) ∈
      {y : OddCost | z.2 + 2 * Real.log 3 < y.2}} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have h1 := draw_cost_le_log_three (s := x.1.1) (by linarith [x.1.2])
    have h2 := draw_cost_le_log_three (s := x.2.1) (by linarith [x.2.2])
    change z.2 + 2 * Real.log 3 < z.2 + cost x.1.1 + cost x.2.1 at hx
    linarith
  rw [he, measure_empty]

theorem costKilled_cost_upper (z : OddCost) :
    ∀ᵐ y ∂costKilled z, y.2 ≤ z.2 + 2 * Real.log 3 := ae_restrict_of_ae (pairedCost_cost_upper z)

theorem costKilled_pow_cost_upper (n : ℕ) (z : OddCost) :
    ∀ᵐ y ∂(costKilled ^ n) z, y.2 ≤ z.2 + 2 * (n : ℝ) * Real.log 3 := by
  induction n generalizing z with
  | zero =>
    simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
    change ∀ᵐ y ∂Measure.dirac z, y.2 ≤ z.2
    exact (ae_dirac_iff (measurableSet_le measurable_snd measurable_const)).mpr le_rfl
  | succ n ih =>
    have hp : costKilled ^ (n + 1) = costKilled ∘ₖ (costKilled ^ n) := pow_succ' costKilled n
    rw [hp]
    apply Kernel.ae_comp_of_ae_ae (measurableSet_le measurable_snd measurable_const)
    filter_upwards [ih z] with y hy
    filter_upwards [costKilled_cost_upper y] with w hw
    push_cast
    nlinarith

theorem captured_cost_upper (z : OddCost) :
    ∀ᵐ y ∂costCaptured z, y.2 ≤ z.2 + 2 * Real.log 3 := ae_restrict_of_ae (pairedCost_cost_upper z)

theorem firstReturn_cost_upper (n : ℕ) (z : OddCost) :
    ∀ᵐ y ∂firstReturn n z, y.2 ≤ z.2 + 2 * ((n + 1 : ℕ) : ℝ) * Real.log 3 := by
  rw [firstReturn]
  apply Kernel.ae_comp_of_ae_ae (measurableSet_le measurable_snd measurable_const)
  filter_upwards [costKilled_pow_cost_upper n z] with y hy
  filter_upwards [captured_cost_upper y] with w hw
  push_cast
  nlinarith

theorem markedReturn_cost_upper (z : OddCost) :
    ∀ᵐ x ∂markedReturnLaw z, x.2.2 ≤ z.2 + (x.1 : ℝ) * Real.log 3 := by
  rw [markedReturnLaw, Kernel.sum_apply, Measure.ae_sum_iff]
  intro n
  rw [firstMarkedReturn, Kernel.map_apply _ (markReturn_measurable n)]
  have hm : Measurable (fun x : MarkedReturn => z.2 + (x.1 : ℝ) * Real.log 3) :=
    measurable_const.add (((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp measurable_fst).mul measurable_const)
  apply (ae_map_iff (markReturn_measurable n).aemeasurable
    (measurableSet_le (measurable_snd.comp measurable_snd) hm)).mpr
  filter_upwards [firstReturn_cost_upper n z] with x hx
  change x.2 ≤ z.2 + ((2 * (n + 1) : ℕ) : ℝ) * Real.log 3
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hx

theorem markedCycle_cost_upper : ∀ᵐ x ∂markedCycleLaw, x.2.2 ≤ (x.1 : ℝ) * Real.log 3 := by
  have h := markedReturn_cost_upper (RegenerationTails.regenerationState, 0)
  convert! h using 1
  simp

theorem cycle_cost_exponential_moment : ∃ η : ℝ, 0 < η ∧
    (∫⁻ G, ENNReal.ofReal (Real.exp (η * G)) ∂cycleCostLaw) < ∞ := by
  obtain ⟨θ, hθ, hb⟩ := return_duration_exponential_moment
  have hL : 0 < Real.log 3 := Real.log_pos (by norm_num)
  let η := θ / Real.log 3
  have hη : 0 < η := div_pos hθ hL
  refine ⟨η, hη, ?_⟩
  rw [← markedCycleLaw_cost_projection,
    lintegral_map (g := fun x : MarkedReturn => x.2.2) (f := fun G : ℝ => ENNReal.ofReal (Real.exp (η * G)))
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul measurable_id)))
      (measurable_snd.comp measurable_snd)]
  have hbound : (∫⁻ x : MarkedReturn, ENNReal.ofReal (Real.exp (η * x.2.2)) ∂markedCycleLaw) ≤
      ∫⁻ x : MarkedReturn, ENNReal.ofReal (Real.exp (θ * (x.1 : ℝ))) ∂markedCycleLaw := by
    apply lintegral_mono_ae
    filter_upwards [markedCycle_cost_upper] with x hx
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have heq : η * ((x.1 : ℝ) * Real.log 3) = θ * (x.1 : ℝ) := by dsimp [η]; field_simp [ne_of_gt hL]
    nlinarith [mul_le_mul_of_nonneg_left hx hη.le]
  apply lt_of_le_of_lt hbound
  have h := hb (RegenerationTails.regenerationState, 0)
  rw [durationFrom, lintegral_map (measurable_of_countable (fun n : ℕ => ENNReal.ofReal (Real.exp (θ * (n : ℝ))))) measurable_fst] at h
  exact h

theorem cycle_cost_exponential_integrable : ∃ η : ℝ, 0 < η ∧
    Integrable (fun G : ℝ => Real.exp (η * G)) cycleCostLaw := by
  obtain ⟨η, hη, hb⟩ := cycle_cost_exponential_moment
  refine ⟨η, hη, ⟨(Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable, ?_⟩⟩
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun G : ℝ => (Real.exp_pos (η * G)).le))).mpr hb

end NumberTheoryLean.CycleCostMoments

end

section

namespace NumberTheoryLean.CycleOccupation

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostProcess PairedCostGrouping
open CostReturnLaw CycleCostLower CycleCostMoments

noncomputable def pairSampling : Kernel OddCost (OddCost × (EvenState × OddState)) :=
  Kernel.id ×ₖ pairedDraws.prodMkRight ℝ

instance pairSampling_isMarkovKernel : IsMarkovKernel pairSampling := by unfold pairSampling; infer_instance

noncomputable def evenVisitMap (x : OddCost × (EvenState × OddState)) : CostState :=
  (.inl x.2.1, x.1.2 + cost x.2.1.1)

noncomputable def oddVisitMap (x : OddCost × (EvenState × OddState)) : CostState :=
  (.inr x.2.2, x.1.2 + cost x.2.1.1 + cost x.2.2.1)

theorem evenVisitMap_measurable : Measurable evenVisitMap :=
  (measurable_inl.comp (measurable_fst.comp measurable_snd)).prodMk
    ((measurable_snd.comp measurable_fst).add
      (cost_measurable.comp (measurable_subtype_coe.comp (measurable_fst.comp measurable_snd))))

theorem oddVisitMap_measurable : Measurable oddVisitMap :=
  (measurable_inr.comp (measurable_snd.comp measurable_snd)).prodMk
    (((measurable_snd.comp measurable_fst).add
      (cost_measurable.comp (measurable_subtype_coe.comp (measurable_fst.comp measurable_snd)))).add
      (cost_measurable.comp (measurable_subtype_coe.comp (measurable_snd.comp measurable_snd))))

noncomputable def evenVisit : Kernel OddCost CostState := pairSampling.map evenVisitMap
noncomputable def oddVisit : Kernel OddCost CostState := pairSampling.map oddVisitMap

instance evenVisit_isMarkovKernel : IsMarkovKernel evenVisit := Kernel.IsMarkovKernel.map _ evenVisitMap_measurable
instance oddVisit_isMarkovKernel : IsMarkovKernel oddVisit := Kernel.IsMarkovKernel.map _ oddVisitMap_measurable

theorem sampling_map_measure {α : Type*} [MeasurableSpace α]
    (f : OddCost × (EvenState × OddState) → α) (hf : Measurable f) (z : OddCost) :
    (pairSampling.map f) z = (pairedDraws z.1).map (fun x => f (z, x)) := by
  ext B hB
  rw [Kernel.map_apply' _ hf _ hB, pairSampling,
    Kernel.prod_apply' _ _ _ (hf hB), Kernel.id_apply, lintegral_dirac']
  · rw [Measure.map_apply (f := fun x : EvenState × OddState => f (z, x)) (hf.comp measurable_prodMk_left) hB]
    rfl
  · exact measurable_measure_prodMk_left (hf hB)

theorem evenVisit_eq_full_step (z : OddCost) : evenVisit z = costKernel (embedOdd z) := by
  apply Measure.ext_of_lintegral
  intro H hH
  rw [evenVisit, sampling_map_measure _ evenVisitMap_measurable,
    lintegral_map (g := fun x : EvenState × OddState => evenVisitMap (z, x)) hH
      (evenVisitMap_measurable.comp measurable_prodMk_left), pairedDraws,
    Kernel.lintegral_compProd _ _ _ (f := fun x : EvenState × OddState => H (evenVisitMap (z, x)))
      (hH.comp (evenVisitMap_measurable.comp measurable_prodMk_left))]
  change (∫⁻ t : EvenState, ∫⁻ _u : OddState, H (.inl t, z.2 + cost t.1) ∂evenToOdd t ∂oddToEven z.1) = _
  simp only [lintegral_const, measure_univ, mul_one]
  exact (costKernel_odd_lintegral z.1 z.2 hH).symm

theorem oddVisit_eq_paired (z : OddCost) : oddVisit z = (pairedCostKernel z).map embedOdd := by
  have h : oddVisit = pairedCostKernel.map embedOdd := by
    rw [oddVisit, pairedCostKernel, ← Kernel.map_comp_right _ pairUpdate_measurable embedOdd_measurable]
    rfl
  rw [h, Kernel.map_apply _ embedOdd_measurable]

noncomputable def pairVisits : Kernel OddCost CostState := evenVisit + oddVisit

instance pairVisits_isFiniteKernel : IsFiniteKernel pairVisits := by unfold pairVisits; infer_instance

theorem pairVisits_full_steps (z : OddCost) :
    pairVisits z = costKernel (embedOdd z) + (costKernel ^ 2) (embedOdd z) := by
  rw [pairVisits, add_apply, evenVisit_eq_full_step, oddVisit_eq_paired, pairedCost_full_grouping]

theorem pairVisits_mass (z : OddCost) : pairVisits z univ = 2 := by
  rw [pairVisits, add_apply, Measure.add_apply]
  simp only [measure_univ]
  norm_num

theorem evenVisit_age_bounds (z : OddCost) :
    ∀ᵐ y ∂evenVisit z, z.2 ≤ y.2 ∧ y.2 ≤ z.2 + 2 * Real.log 3 := by
  rw [evenVisit, sampling_map_measure _ evenVisitMap_measurable]
  apply (ae_map_iff (evenVisitMap_measurable.comp measurable_prodMk_left).aemeasurable
    ((measurableSet_le measurable_const measurable_snd).inter (measurableSet_le measurable_snd measurable_const))).mpr
  apply Eventually.of_forall
  intro x
  have hp : 0 < cost x.1.1 := cost_pos (by linarith [x.1.2])
  have hu := draw_cost_le_log_three (s := x.1.1) (by linarith [x.1.2])
  have hL : 0 < Real.log 3 := Real.log_pos (by norm_num)
  change z.2 ≤ z.2 + cost x.1.1 ∧ z.2 + cost x.1.1 ≤ z.2 + 2 * Real.log 3
  constructor <;> linarith

theorem oddVisit_age_bounds (z : OddCost) :
    ∀ᵐ y ∂oddVisit z, z.2 ≤ y.2 ∧ y.2 ≤ z.2 + 2 * Real.log 3 := by
  rw [oddVisit, sampling_map_measure _ oddVisitMap_measurable]
  apply (ae_map_iff (oddVisitMap_measurable.comp measurable_prodMk_left).aemeasurable
    ((measurableSet_le measurable_const measurable_snd).inter (measurableSet_le measurable_snd measurable_const))).mpr
  apply Eventually.of_forall
  intro x
  have hp : 0 < cost x.1.1 := cost_pos (by linarith [x.1.2])
  have hq : 0 < cost x.2.1 := cost_pos (by linarith [x.2.2])
  have hu := draw_cost_le_log_three (s := x.1.1) (by linarith [x.1.2])
  have hv := draw_cost_le_log_three (s := x.2.1) (by linarith [x.2.2])
  change z.2 ≤ z.2 + cost x.1.1 + cost x.2.1 ∧
    z.2 + cost x.1.1 + cost x.2.1 ≤ z.2 + 2 * Real.log 3
  constructor <;> linarith

theorem pairVisits_age_bounds (z : OddCost) :
    ∀ᵐ y ∂pairVisits z, z.2 ≤ y.2 ∧ y.2 ≤ z.2 + 2 * Real.log 3 := by
  rw [pairVisits, add_apply, ae_add_measure_iff]
  exact ⟨evenVisit_age_bounds z, oddVisit_age_bounds z⟩

noncomputable def visitBlock (n : ℕ) : Kernel OddCost CostState := pairVisits ∘ₖ (costKilled ^ n)

instance visitBlock_isFiniteKernel (n : ℕ) : IsFiniteKernel (visitBlock n) := by unfold visitBlock; infer_instance

theorem visitBlock_mass (n : ℕ) (z : OddCost) : visitBlock n z univ = 2 * (costKilled ^ n) z univ := by
  rw [visitBlock, Kernel.comp_apply' _ _ _ MeasurableSet.univ]
  simp only [pairVisits_mass, lintegral_const]

theorem visitBlock_age_bounds (n : ℕ) (z : OddCost) :
    ∀ᵐ y ∂visitBlock n z, z.2 ≤ y.2 ∧ y.2 ≤ z.2 + 2 * ((n + 1 : ℕ) : ℝ) * Real.log 3 := by
  rw [visitBlock]
  apply Kernel.ae_comp_of_ae_ae
    ((measurableSet_le measurable_const measurable_snd).inter (measurableSet_le measurable_snd measurable_const))
  filter_upwards [costKilled_pow_cost_monotone n z, costKilled_pow_cost_upper n z] with w hwL hwU
  filter_upwards [pairVisits_age_bounds w] with y hy
  constructor
  · exact le_trans hwL hy.1
  · calc
      y.2 ≤ w.2 + 2 * Real.log 3 := hy.2
      _ ≤ (z.2 + 2 * (n : ℝ) * Real.log 3) + 2 * Real.log 3 := add_le_add hwU le_rfl
      _ = _ := by push_cast; ring

noncomputable def occupationKernel : Kernel OddCost CostState := Kernel.sum visitBlock

instance occupationKernel_isSFiniteKernel : IsSFiniteKernel occupationKernel := by unfold occupationKernel; infer_instance

noncomputable def occupationMeasure : Measure CostState := occupationKernel (RegenerationTails.regenerationState, 0)

theorem occupation_age_nonneg : ∀ᵐ y ∂occupationMeasure, 0 ≤ y.2 := by
  rw [occupationMeasure, occupationKernel, Kernel.sum_apply, Measure.ae_sum_iff]
  intro n
  exact (visitBlock_age_bounds n (RegenerationTails.regenerationState, 0)).mono (fun _ h => h.1)

theorem occupationFrom_exponential_moment : ∃ η : ℝ, 0 < η ∧ ∀ z : OddCost,
    (∫⁻ y, ENNReal.ofReal (Real.exp (η * (y.2 - z.2))) ∂occupationKernel z) < ∞ := by
  obtain ⟨m, hm, ρ, D, hρ, hρ1, hD, hb⟩ := PairedBlockContraction.paired_survival_geometric
  let θ := -Real.log ρ / (4 * (m : ℝ))
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hθ : 0 < θ := div_pos (neg_pos.mpr (Real.log_neg hρ hρ1)) (by positivity)
  have hrel : 4 * (m : ℝ) * θ = -Real.log ρ := by dsimp [θ]; field_simp
  have hL : 0 < Real.log 3 := Real.log_pos (by norm_num)
  let η := θ / Real.log 3
  have hη : 0 < η := div_pos hθ hL
  refine ⟨η, hη, ?_⟩
  intro z
  let A := 2 * Real.exp (-Real.log ρ + 2 * θ) * (PairedDrift.V z.1 + D)
  let r := Real.exp (-2 * θ)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hsum : Summable (fun n : ℕ => A * r ^ n) := (summable_geometric_of_lt_one hr0 hr1).mul_left A
  rw [occupationKernel, Kernel.sum_apply, lintegral_sum_measure]
  apply lt_of_le_of_lt (ENNReal.tsum_le_tsum ?_) hsum.tsum_ofReal_lt_top
  intro n
  have hW : 0 < PairedDrift.V z.1 + D := add_pos (PairedDrift.V_pos z.1) hD
  have hn := CycleDurationMoments.weighted_geometric_bound hm hρ hθ hrel n
  have hsurv : (costKilled ^ n) z univ ≤ ENNReal.ofReal (ρ ^ (n / m) * (PairedDrift.V z.1 + D)) := by
    rw [costKilled_mass]
    exact le_trans (PairedHitting.paired_survival_antitone z.1 (Nat.mul_div_le n m)) (hb (n / m) z.1)
  calc
    _ ≤ ∫⁻ _y, ENNReal.ofReal (Real.exp (θ * (2 * ((n : ℝ) + 1)))) ∂visitBlock n z := by
      apply lintegral_mono_ae
      filter_upwards [visitBlock_age_bounds n z] with y hy
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      calc
        η * (y.2 - z.2) ≤ η * (2 * ((n + 1 : ℕ) : ℝ) * Real.log 3) :=
          mul_le_mul_of_nonneg_left (by linarith [hy.2]) hη.le
        _ = θ * (2 * ((n : ℝ) + 1)) := by dsimp [η]; push_cast; field_simp
    _ = ENNReal.ofReal (Real.exp (θ * (2 * ((n : ℝ) + 1)))) *
        (2 * (costKilled ^ n) z univ) := by rw [lintegral_const, visitBlock_mass]
    _ ≤ ENNReal.ofReal (Real.exp (θ * (2 * ((n : ℝ) + 1)))) *
        (2 * ENNReal.ofReal (ρ ^ (n / m) * (PairedDrift.V z.1 + D))) :=
      mul_le_mul le_rfl (mul_le_mul le_rfl hsurv zero_le zero_le) zero_le zero_le
    _ = ENNReal.ofReal (2 * (Real.exp (θ * (2 * ((n : ℝ) + 1)))) * ρ ^ (n / m) * (PairedDrift.V z.1 + D)) := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (A * r ^ n) := ENNReal.ofReal_le_ofReal (by
      dsimp [A, r]
      nlinarith [mul_le_mul_of_nonneg_right hn hW.le])

theorem occupation_exponential_moment : ∃ η : ℝ, 0 < η ∧
    (∫⁻ y, ENNReal.ofReal (Real.exp (η * y.2)) ∂occupationMeasure) < ∞ := by
  obtain ⟨η, hη, hb⟩ := occupationFrom_exponential_moment
  exact ⟨η, hη, by simpa only [occupationMeasure, sub_zero] using hb (RegenerationTails.regenerationState, 0)⟩

instance occupationMeasure_isFiniteMeasure : IsFiniteMeasure occupationMeasure := by
  obtain ⟨η, hη, hb⟩ := occupation_exponential_moment
  constructor
  apply lt_of_le_of_lt (show occupationMeasure univ ≤ ∫⁻ y, ENNReal.ofReal (Real.exp (η * y.2)) ∂occupationMeasure from ?_) hb
  calc
    _ = ∫⁻ _y, (1 : ℝ≥0∞) ∂occupationMeasure := by simp
    _ ≤ _ := by
      apply lintegral_mono_ae
      filter_upwards [occupation_age_nonneg] with y hy
      exact ENNReal.one_le_ofReal.mpr (Real.one_le_exp (mul_nonneg hη.le hy))

theorem occupation_exponential_integrable : ∃ η : ℝ, 0 < η ∧
    Integrable (fun y : CostState => Real.exp (η * y.2)) occupationMeasure := by
  obtain ⟨η, hη, hb⟩ := occupation_exponential_moment
  refine ⟨η, hη, (Real.measurable_exp.comp (measurable_const.mul measurable_snd)).aestronglyMeasurable, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall
    (fun y : CostState => (Real.exp_pos (η * y.2)).le))).mpr hb

end NumberTheoryLean.CycleOccupation

end

section

namespace NumberTheoryLean.CycleRenewalInputs

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
open CostReturnLaw CycleCostLower CycleCostMoments CycleCostAtomless
open AbsorptionCutoff.Renewal

theorem cycle_negative_exponential_integrable {η : ℝ} (hη : 0 ≤ η) :
    Integrable (fun G : ℝ => Real.exp (-η * G)) cycleCostLaw := by
  refine (integrable_const (1 : ℝ)).mono'
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable) ?_
  filter_upwards [cycleCostLaw_positive] with G hG
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (by nlinarith)

theorem cycle_all_moments (n : ℕ) : Integrable (fun G : ℝ => G ^ n) cycleCostLaw := by
  obtain ⟨η, hη, hp⟩ := cycle_cost_exponential_integrable
  have hn := cycle_negative_exponential_integrable hη.le
  simpa only [id_eq] using integrable_pow_of_integrable_exp_mul (μ := cycleCostLaw)
    (X := id) (ne_of_gt hη) hp hn n

theorem cycle_integrable_id : Integrable id cycleCostLaw := by
  convert! cycle_all_moments 1 using 1
  simp
  rfl

theorem cycle_memLp_two : MemLp id 2 cycleCostLaw := by
  apply (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr
  exact cycle_all_moments 2

theorem cycle_mean_lower : Real.log (4 / 3) ≤ ∫ G : ℝ, G ∂cycleCostLaw := by
  have h := integral_mono_ae (integrable_const (Real.log (4 / 3))) cycle_integrable_id cycleCostLaw_lower
  simpa using h

theorem cycle_mean_pos : 0 < ∫ G : ℝ, G ∂cycleCostLaw :=
  lt_of_lt_of_le (Real.log_pos (by norm_num)) cycle_mean_lower

theorem cycle_nonlattice : Nonlattice cycleCostLaw := by
  intro a r
  rw [cycleCostLaw_lattice_null]
  norm_num

theorem cycle_expTransform_le : expTransform 1 cycleCostLaw ≤ ENNReal.ofReal (3 / 4 : ℝ) := by
  unfold expTransform
  simp only [one_mul]
  have heq : Real.exp (-Real.log (4 / 3)) = (3 : ℝ) / 4 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)]
    norm_num
  calc
    _ ≤ ∫⁻ _G : ℝ, ENNReal.ofReal (Real.exp (-Real.log (4 / 3))) ∂cycleCostLaw := by
      apply lintegral_mono_ae
      filter_upwards [cycleCostLaw_lower] with G hG
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith))
    _ = _ := by rw [lintegral_const, measure_univ, mul_one, heq]

theorem cycle_expTransform_lt_one : expTransform 1 cycleCostLaw < 1 :=
  lt_of_le_of_lt cycle_expTransform_le (by norm_num)

theorem cycle_key_renewal {H : ℝ → ℝ} (hH : Continuous H)
    (hDRI : driNorm (fun x => ‖H x‖ₑ) ≠ ∞) :
    Tendsto (fun y : ℝ => ∑' n : ℕ, ∫ s, H (y - s) ∂convPow cycleCostLaw n)
      atTop (𝓝 ((∫ x : ℝ, H x) / (∫ G : ℝ, G ∂cycleCostLaw))) :=
  tendsto_tsum_integral_comp_sub_of_driNorm_real cycle_nonlattice cycle_memLp_two cycle_mean_pos
    (θ := 1) (by norm_num) cycle_expTransform_lt_one hH hDRI

theorem cycle_renewal_cell_bound (ell : ℝ) : ∃ C : ℝ, ∀ y : ℝ,
    renewalMeasure cycleCostLaw (Icc y (y + ell)) ≤ ENNReal.ofReal C :=
  exists_bound_renewalMeasure_Icc_of_expTransform cycle_nonlattice cycle_memLp_two cycle_mean_pos
    (θ := 1) (by norm_num) cycle_expTransform_lt_one ell

end NumberTheoryLean.CycleRenewalInputs

end

section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
namespace Erdos970Dependency.ActualCycleOccupation
open NumberTheoryLean.TransitionKernels NumberTheoryLean.FinitePathGeometry NumberTheoryLean.FinitePathMeasures
open NumberTheoryLean.PairedHitting NumberTheoryLean.PairedCostProcess NumberTheoryLean.PairedCostGrouping
open NumberTheoryLean.CostReturnLaw NumberTheoryLean.CycleOccupation NumberTheoryLean.KernelPotential
open Erdos970Dependency.InvariantDensities Erdos970Dependency.StateKernelInvariance
open Erdos970Dependency.RegenerativeOddOccupation

theorem costKernel_map_state (z : CostState) : (costKernel z).map Prod.fst = stateKernel z.1 := by
  have hm : Measurable (fun s : State ↦ (s, z.2 + cost (stateRatio s))) :=
    measurable_id.prodMk (measurable_const.add (cost_measurable.comp stateRatio_measurable))
  rw [costKernel_eq_map, Measure.map_map measurable_fst hm]
  change (stateKernel z.1).map id = stateKernel z.1
  exact Measure.map_id

theorem evenVisit_map_state (z : OddCost) :
    (evenVisit z).map Prod.fst = (oddToEven z.1).map Sum.inl := by
  rw [evenVisit_eq_full_step, costKernel_map_state]
  change oddBranch z.1 = _
  exact Kernel.map_apply _ measurable_inl _

theorem oddVisit_map_state (z : OddCost) :
    (oddVisit z).map Prod.fst = (pairedOdd z.1).map Sum.inr := by
  rw [oddVisit_eq_paired, Measure.map_map measurable_fst embedOdd_measurable,
    ← pairedCost_map_state z, Measure.map_map measurable_inr measurable_fst]
  rfl

theorem pairVisits_map_state (z : OddCost) : (pairVisits z).map Prod.fst = ratioVisits z.1 := by
  rw [pairVisits, add_apply, Measure.map_add _ _ measurable_fst, evenVisit_map_state, oddVisit_map_state]
  simp only [ratioVisits, add_apply, Kernel.map_apply _ measurable_inl, Kernel.map_apply _ measurable_inr]

theorem visitBlock_map_state (n : ℕ) (z : OddCost) :
    (visitBlock n z).map Prod.fst = (ratioVisits ∘ₖ (pairedKilled ^ n)) z.1 := by
  apply Measure.ext_of_lintegral
  intro H hH
  rw [lintegral_map hH measurable_fst, visitBlock,
    Kernel.lintegral_comp _ _ _ (g := fun y : CostState ↦ H y.1) (hH.comp measurable_fst),
    Kernel.lintegral_comp _ _ _ hH]
  have hi (w : OddCost) : (∫⁻ y : CostState, H y.1 ∂pairVisits w) =
      ∫⁻ s : State, H s ∂ratioVisits w.1 := by
    rw [← pairVisits_map_state w, lintegral_map hH measurable_fst]
  simp_rw [hi]
  have hJ : Measurable (fun s : OddState ↦ ∫⁻ t : State, H t ∂ratioVisits s) := hH.lintegral_kernel
  rw [← costKilled_pow_map_state n z, lintegral_map hJ measurable_fst]

theorem occupation_map_ratioOccupation : occupationMeasure.map Prod.fst = ratioOccupation := by
  rw [occupationMeasure, occupationKernel, Kernel.sum_apply, Measure.map_sum measurable_fst.aemeasurable]
  simp_rw [visitBlock_map_state]
  rw [ratioOccupation, potential, Kernel.sum_apply]

theorem occupation_map_stateMeasure :
    occupationMeasure.map Prod.fst = (ENNReal.ofReal beta)⁻¹ • stateMeasure := by
  rw [occupation_map_ratioOccupation, ratioOccupation_eq]

theorem lintegral_state_occupation {Q : State → ℝ≥0∞} (hQ : Measurable Q) :
    (∫⁻ y : CostState, Q y.1 ∂occupationMeasure) =
      (ENNReal.ofReal beta)⁻¹ * ∫⁻ s : State, Q s ∂stateMeasure := by
  rw [← lintegral_map hQ measurable_fst, occupation_map_stateMeasure, lintegral_smul_measure, smul_eq_mul]

theorem integrable_state_occupation_iff {Q : State → ℝ} (hQ : Measurable Q) :
    Integrable Q stateMeasure ↔ Integrable (fun y : CostState ↦ Q y.1) occupationMeasure := by
  have h := integrable_map_measure (μ := occupationMeasure) (f := Prod.fst) (g := Q)
    hQ.aestronglyMeasurable measurable_fst.aemeasurable
  rw [occupation_map_stateMeasure, integrable_inv_smul_measure
    (ne_of_gt (ENNReal.ofReal_pos.mpr beta_pos)) ENNReal.ofReal_ne_top] at h
  simpa only [Function.comp_def] using h

theorem integral_state_occupation {Q : State → ℝ} (hQ : Measurable Q)
    (hI : Integrable (fun y : CostState ↦ Q y.1) occupationMeasure) :
    Integrable Q stateMeasure ∧
      (∫ y : CostState, Q y.1 ∂occupationMeasure) = (1 / beta) * ∫ s : State, Q s ∂stateMeasure := by
  refine ⟨(integrable_state_occupation_iff hQ).mpr hI, ?_⟩
  rw [← integral_map measurable_fst.aemeasurable hQ.aestronglyMeasurable,
    occupation_map_stateMeasure, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal beta_pos.le, smul_eq_mul, one_div]

end Erdos970Dependency.ActualCycleOccupation

end

section

open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory Topology
namespace Erdos970Dependency.OccupationAge
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess NumberTheoryLean.PairedCostGrouping
open NumberTheoryLean.CostReturnLaw NumberTheoryLean.CycleOccupation NumberTheoryLean.RegenerationTails

theorem oddAge_measurable : Measurable (fun y : OddCost ↦ ENNReal.ofReal y.2) :=
  ENNReal.measurable_ofReal.comp measurable_snd

theorem stateAge_measurable : Measurable (fun y : CostState ↦ ENNReal.ofReal y.2) :=
  ENNReal.measurable_ofReal.comp measurable_snd

theorem occupation_age_integrable : Integrable (fun y : CostState ↦ y.2) occupationMeasure := by
  obtain ⟨eta, heta, hI⟩ := occupation_exponential_integrable
  apply (hI.const_mul (1 / eta)).mono' measurable_snd.aestronglyMeasurable
  filter_upwards [occupation_age_nonneg] with y hy
  rw [Real.norm_of_nonneg hy]
  have h := Real.add_one_le_exp (eta * y.2)
  calc
    y.2 = (1 / eta) * (eta * y.2) := by field_simp
    _ ≤ (1 / eta) * Real.exp (eta * y.2) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

noncomputable def blockAge (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ y : CostState, ENNReal.ofReal y.2 ∂visitBlock n (regenerationState, 0)

noncomputable def residualAge (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ y : OddCost, ENNReal.ofReal y.2 ∂(costKilled ^ n) (regenerationState, 0)

theorem blockAge_sum_finite : (∑' n : ℕ, blockAge n) < ∞ := by
  have heq : (∑' n : ℕ, blockAge n) = ∫⁻ y : CostState, ENNReal.ofReal y.2 ∂occupationMeasure := by
    rw [occupationMeasure, occupationKernel, Kernel.sum_apply, lintegral_sum_measure]
    rfl
  rw [heq, ← ofReal_integral_eq_lintegral_ofReal occupation_age_integrable occupation_age_nonneg]
  exact ENNReal.ofReal_lt_top

theorem blockAge_tendsto_zero : Tendsto blockAge atTop (𝓝 0) :=
  ENNReal.tendsto_atTop_zero_of_tsum_ne_top (ne_of_lt blockAge_sum_finite)

theorem killed_age_le_pair (z : OddCost) :
    (∫⁻ y : OddCost, ENNReal.ofReal y.2 ∂costKilled z) ≤
      ∫⁻ y : CostState, ENNReal.ofReal y.2 ∂pairVisits z := by
  calc
    _ ≤ ∫⁻ y : OddCost, ENNReal.ofReal y.2 ∂pairedCostKernel z :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ∫⁻ y : CostState, ENNReal.ofReal y.2 ∂oddVisit z := by
      rw [oddVisit_eq_paired, lintegral_map stateAge_measurable embedOdd_measurable]
      rfl
    _ ≤ _ := lintegral_mono' (by
      rw [pairVisits, add_apply]
      apply Measure.le_iff.mpr
      intro B _
      rw [Measure.add_apply]
      exact le_add_left le_rfl) le_rfl

theorem residualAge_succ_le (n : ℕ) : residualAge (n + 1) ≤ blockAge n := by
  have hp : costKilled ^ (n + 1) = costKilled ∘ₖ (costKilled ^ n) := pow_succ' costKilled n
  rw [residualAge, hp,
    Kernel.lintegral_comp _ _ _ oddAge_measurable,
    blockAge, visitBlock,
    Kernel.lintegral_comp _ _ _ stateAge_measurable]
  exact lintegral_mono killed_age_le_pair

theorem residualAge_tendsto_zero : Tendsto residualAge atTop (𝓝 0) := by
  have hshift : Tendsto (fun n : ℕ ↦ residualAge (n + 1)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds blockAge_tendsto_zero
      (Eventually.of_forall (fun _ ↦ zero_le)) (Eventually.of_forall residualAge_succ_le)
  exact (tendsto_add_atTop_iff_nat 1).mp hshift

end Erdos970Dependency.OccupationAge

end

end Erdos970

end OAI
