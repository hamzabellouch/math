import OAI.NumberTheory.Jacobsthal.Estimates.InitialOddDraw
import OAI.NumberTheory.Jacobsthal.Estimates.OnePairCost

namespace OAI

namespace Erdos970

section

open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory Topology BigOperators
namespace Erdos970Dependency.CycleMeanCost
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.PairedCostProcess
open NumberTheoryLean.CostReturnLaw NumberTheoryLean.CycleCostLower NumberTheoryLean.CycleOccupation
open NumberTheoryLean.RegenerationTails
open Erdos970Dependency.InvariantDensities Erdos970Dependency.InvariantCostBound
open Erdos970Dependency.RawStateCost Erdos970Dependency.OccupationAge Erdos970Dependency.OnePairCost

noncomputable def capturedAge (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ y : OddCost, ENNReal.ofReal y.2 ∂firstReturn n (regenerationState, 0)

noncomputable def blockIncrement (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ y : CostState, ENNReal.ofReal (stateCost y.1) ∂visitBlock n (regenerationState, 0)

theorem residualAge_zero : residualAge 0 = 0 := by
  change (∫⁻ y : OddCost, ENNReal.ofReal y.2 ∂Measure.dirac (regenerationState, 0)) = 0
  rw [lintegral_dirac' _ oddAge_measurable]
  norm_num

theorem age_balance (n : ℕ) : capturedAge n + residualAge (n + 1) = residualAge n + blockIncrement n := by
  have hp : costKilled ^ (n + 1) = costKilled ∘ₖ (costKilled ^ n) := pow_succ' costKilled n
  simp only [capturedAge, residualAge, blockIncrement, firstReturn, visitBlock]
  rw [hp, Kernel.lintegral_comp _ _ _ oddAge_measurable,
    Kernel.lintegral_comp _ _ _ oddAge_measurable,
    Kernel.lintegral_comp _ _ _ increment_test_measurable]
  have hC : Measurable (fun z : OddCost ↦ ∫⁻ y : OddCost, ENNReal.ofReal y.2 ∂costCaptured z) :=
    oddAge_measurable.lintegral_kernel
  rw [← lintegral_add_left hC, ← lintegral_add_left oddAge_measurable]
  apply lintegral_congr_ae
  filter_upwards [costKilled_pow_cost_monotone n (regenerationState, 0)] with z hz
  exact captured_killed_age_balance z hz

theorem finite_cost_balance (N : ℕ) :
    (∑ n ∈ Finset.range N, capturedAge n) + residualAge N = ∑ n ∈ Finset.range N, blockIncrement n := by
  induction N with
  | zero => simp [residualAge_zero]
  | succ N ih =>
    calc
      _ = ((∑ n ∈ Finset.range N, capturedAge n) + capturedAge N) + residualAge (N + 1) := by
        rw [Finset.sum_range_succ]
      _ = ((∑ n ∈ Finset.range N, capturedAge n) + residualAge N) + blockIncrement N := by
        rw [add_assoc, age_balance, ← add_assoc]
      _ = (∑ n ∈ Finset.range N, blockIncrement n) + blockIncrement N := by rw [ih]
      _ = _ := (Finset.sum_range_succ _ _).symm

theorem capturedAge_sum : (∑' n : ℕ, capturedAge n) =
    ∫⁻ G : ℝ, ENNReal.ofReal G ∂cycleCostLaw := by
  rw [cycleCostLaw, lintegral_map ENNReal.measurable_ofReal measurable_snd,
    returnLaw, Kernel.sum_apply, lintegral_sum_measure]
  rfl

theorem blockIncrement_sum : (∑' n : ℕ, blockIncrement n) =
    ∫⁻ y : CostState, ENNReal.ofReal (stateCost y.1) ∂occupationMeasure := by
  rw [occupationMeasure, occupationKernel, Kernel.sum_apply, lintegral_sum_measure]
  rfl

theorem cycle_cost_lintegral_eq_increments :
    (∫⁻ G : ℝ, ENNReal.ofReal G ∂cycleCostLaw) =
      ∫⁻ y : CostState, ENNReal.ofReal (stateCost y.1) ∂occupationMeasure := by
  have hleft : Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.range N, capturedAge n) + residualAge N)
      atTop (𝓝 (∑' n : ℕ, capturedAge n)) := by
    simpa only [add_zero] using (ENNReal.tendsto_nat_tsum capturedAge).add residualAge_tendsto_zero
  have hleft' : Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.range N, blockIncrement n)
      atTop (𝓝 (∑' n : ℕ, capturedAge n)) :=
    hleft.congr' (Eventually.of_forall finite_cost_balance)
  have h := tendsto_nhds_unique hleft' (ENNReal.tendsto_nat_tsum blockIncrement)
  rw [capturedAge_sum, blockIncrement_sum] at h
  exact h

theorem cycle_cost_integrable : Integrable (fun G : ℝ ↦ G) cycleCostLaw := by
  have hc : ∀ᵐ G ∂cycleCostLaw, 0 ≤ G := cycleCostLaw_positive.mono (fun _ h ↦ h.le)
  have ho : ∀ᵐ y : CostState ∂occupationMeasure, 0 ≤ stateCost y.1 :=
    Eventually.of_forall (fun y ↦ (stateCost_bounds y.1).1.le)
  refine ⟨measurable_id.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hc).mpr ?_⟩
  rw [cycle_cost_lintegral_eq_increments,
    ← ofReal_integral_eq_lintegral_ofReal occupation_increment_integrable ho]
  exact ENNReal.ofReal_lt_top

theorem cycle_mean_eq : (∫ G : ℝ, G ∂cycleCostLaw) = costMass / beta := by
  have hc : ∀ᵐ G ∂cycleCostLaw, 0 ≤ G := cycleCostLaw_positive.mono (fun _ h ↦ h.le)
  have ho : ∀ᵐ y : CostState ∂occupationMeasure, 0 ≤ stateCost y.1 :=
    Eventually.of_forall (fun y ↦ (stateCost_bounds y.1).1.le)
  have h := cycle_cost_lintegral_eq_increments
  rw [← ofReal_integral_eq_lintegral_ofReal cycle_cost_integrable hc,
    ← ofReal_integral_eq_lintegral_ofReal occupation_increment_integrable ho] at h
  have hr := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_ofReal (integral_nonneg_of_ae hc),
    ENNReal.toReal_ofReal (integral_nonneg_of_ae ho)] at hr
  exact hr.trans occupation_increment_integral

end Erdos970Dependency.CycleMeanCost

end

section

namespace NumberTheoryLean.InitialRegeneration

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostProcess
open CostReturnLaw CycleRegeneration CycleCostLower PairedDrift
open UniformCycleMoments InitialOddDraw

noncomputable def hitOrReturn : Kernel OddCost OddCost := by
  classical
  exact Kernel.piecewise returnSet_measurable Kernel.id returnLaw

instance hitOrReturn_isMarkovKernel : IsMarkovKernel hitOrReturn := by unfold hitOrReturn; infer_instance

theorem hitOrReturn_ae_regeneration (z : OddCost) : ∀ᵐ w ∂hitOrReturn z, w ∈ returnSet := by
  classical
  rw [hitOrReturn, Kernel.piecewise_apply]
  split_ifs with hz
  · rw [Kernel.id_apply]
    exact (ae_dirac_iff returnSet_measurable).mpr hz
  · exact returnLaw_ae_regeneration z

theorem hitOrReturn_cost_monotone (z : OddCost) : ∀ᵐ w ∂hitOrReturn z, z.2 ≤ w.2 := by
  classical
  rw [hitOrReturn, Kernel.piecewise_apply]
  split_ifs
  · rw [Kernel.id_apply]
    exact (ae_dirac_iff (measurableSet_le measurable_const measurable_snd)).mpr le_rfl
  · filter_upwards [returnLaw_cost_lower z] with w hw
    have hc : 0 < cost (3 : ℝ) := cost_pos (by norm_num)
    linarith

noncomputable def delayedRegeneration : Kernel EvenState OddCost := hitOrReturn ∘ₖ firstOdd

instance delayedRegeneration_isMarkovKernel : IsMarkovKernel delayedRegeneration := by
  unfold delayedRegeneration
  infer_instance

theorem delayedRegeneration_ae_regeneration (s : EvenState) :
    ∀ᵐ z ∂delayedRegeneration s, z ∈ returnSet := by
  rw [delayedRegeneration]
  exact Kernel.ae_comp_of_ae_ae returnSet_measurable (Eventually.of_forall hitOrReturn_ae_regeneration)

theorem delayedRegeneration_cost_nonneg (s : EvenState) :
    ∀ᵐ z ∂delayedRegeneration s, 0 ≤ z.2 := by
  rw [delayedRegeneration]
  apply Kernel.ae_comp_of_ae_ae (measurableSet_le measurable_const measurable_snd)
  filter_upwards [firstOdd_cost_bounds s] with z hz
  filter_upwards [hitOrReturn_cost_monotone z] with w hw
  exact le_trans hz.1 hw

theorem exponential_total_eq {α : Type*} [MeasurableSpace α]
    (μ : Measure (α × ℝ)) (η T : ℝ) :
    (∫⁻ y, ENNReal.ofReal (Real.exp (η * y.2)) ∂μ) =
      ENNReal.ofReal (Real.exp (η * T)) *
        (∫⁻ y, ENNReal.ofReal (Real.exp (η * (y.2 - T))) ∂μ) := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro y
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

theorem delayedRegeneration_uniform_exponential (S : ℝ) :
    ∃ η B : ℝ, 0 < η ∧ 0 ≤ B ∧ ∀ s : EvenState, s.1 ≤ S →
      (∫⁻ z, ENNReal.ofReal (Real.exp (η * z.2)) ∂delayedRegeneration s) ≤ ENNReal.ofReal B := by
  classical
  obtain ⟨η, C, D, hη, hC, hD, hb⟩ := return_increment_uniform_exponential
  have hpoint : ∀ z : OddCost,
      (∫⁻ w, ENNReal.ofReal (Real.exp (η * w.2)) ∂hitOrReturn z) ≤
        ENNReal.ofReal (C + 1) * ENNReal.ofReal (Real.exp (η * z.2) * (V z.1 + (D + 1))) := by
    intro z
    rw [hitOrReturn, Kernel.piecewise_apply]
    split_ifs
    · rw [Kernel.id_apply, lintegral_dirac' z (f := fun w : OddCost => ENNReal.ofReal (Real.exp (η * w.2)))
        (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul measurable_snd))),
        ← ENNReal.ofReal_mul (by linarith : 0 ≤ C + 1)]
      apply ENNReal.ofReal_le_ofReal
      have hV : 1 ≤ V z.1 := V_one_le z.1
      have hw : 1 ≤ (C + 1) * (V z.1 + (D + 1)) := by nlinarith [mul_nonneg hC (by linarith : 0 ≤ V z.1 + (D + 1))]
      nlinarith [mul_le_mul_of_nonneg_left hw (Real.exp_pos (η * z.2)).le]
    · rw [exponential_total_eq _ η z.2]
      calc
        _ ≤ ENNReal.ofReal (Real.exp (η * z.2)) * ENNReal.ofReal (C * (V z.1 + D)) :=
          mul_le_mul le_rfl (hb z) zero_le zero_le
        _ ≤ _ := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
            ← ENNReal.ofReal_mul (by linarith : 0 ≤ C + 1)]
          apply ENNReal.ofReal_le_ofReal
          have hV : 0 ≤ V z.1 := (V_pos z.1).le
          have hw : C * (V z.1 + D) ≤ (C + 1) * (V z.1 + (D + 1)) := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left hw (Real.exp_pos (η * z.2)).le]
  obtain ⟨B, hB, hfirst⟩ := firstOdd_weighted_exponential S η (D + 1) hη.le (by linarith)
  refine ⟨η, (C + 1) * B, hη, mul_nonneg (by linarith) hB, ?_⟩
  intro s hs
  rw [delayedRegeneration, Kernel.lintegral_comp _ _ _
    (g := fun z : OddCost => ENNReal.ofReal (Real.exp (η * z.2)))
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul measurable_snd)))]
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal (C + 1) * ENNReal.ofReal (Real.exp (η * z.2) * (V z.1 + (D + 1))) ∂firstOdd s :=
      lintegral_mono hpoint
    _ = ENNReal.ofReal (C + 1) *
        (∫⁻ z, ENNReal.ofReal (Real.exp (η * z.2) * (V z.1 + (D + 1))) ∂firstOdd s) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (C + 1) * ENNReal.ofReal B := mul_le_mul le_rfl (hfirst s hs) zero_le zero_le
    _ = _ := (ENNReal.ofReal_mul (by linarith : 0 ≤ C + 1)).symm

noncomputable def delayedCostLaw (s : EvenState) : Measure ℝ := (delayedRegeneration s).map Prod.snd

instance delayedCostLaw_isProbabilityMeasure (s : EvenState) : IsProbabilityMeasure (delayedCostLaw s) :=
  (Measure.isProbabilityMeasure_map_iff (μ := delayedRegeneration s)
    measurable_snd.aemeasurable).mpr inferInstance

theorem delayedCostLaw_uniform_exponential (S : ℝ) : ∃ η B : ℝ, 0 < η ∧ 0 ≤ B ∧
    ∀ s : EvenState, s.1 ≤ S →
      (∫⁻ T, ENNReal.ofReal (Real.exp (η * T)) ∂delayedCostLaw s) ≤ ENNReal.ofReal B := by
  obtain ⟨η, B, hη, hB, hb⟩ := delayedRegeneration_uniform_exponential S
  refine ⟨η, B, hη, hB, ?_⟩
  intro s hs
  rw [delayedCostLaw, lintegral_map (f := fun T : ℝ => ENNReal.ofReal (Real.exp (η * T))) (ENNReal.measurable_ofReal.comp
    (Real.measurable_exp.comp (measurable_const.mul measurable_id))) measurable_snd]
  exact hb s hs

end NumberTheoryLean.InitialRegeneration

end

section

namespace NumberTheoryLean.InitialOccupation

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathMeasures PairedCostProcess PairedCostGrouping
open CostReturnLaw CycleOccupation OccupationDecomposition KernelPotential
open InitialOddDraw InitialRegeneration

noncomputable def beforeRegeneration : Kernel OddCost CostState := by
  classical
  exact Kernel.piecewise returnSet_measurable 0 occupationKernel

instance beforeRegeneration_isSFiniteKernel : IsSFiniteKernel beforeRegeneration := by
  unfold beforeRegeneration
  infer_instance

noncomputable def initialOccupation : Kernel EvenState CostState :=
  firstOdd.map embedOdd + beforeRegeneration ∘ₖ firstOdd

instance initialOccupation_isSFiniteKernel : IsSFiniteKernel initialOccupation := by
  unfold initialOccupation
  infer_instance

theorem pairedOccupation_unfold_cycles :
    pairedOccupation = occupationKernel + pairedOccupation ∘ₖ returnLaw := by
  have hEq : pairedOccupation = potential occupationKernel returnLaw := pairedOccupation_cycle_decomposition
  calc
    _ = potential occupationKernel returnLaw := hEq
    _ = occupationKernel + (potential occupationKernel returnLaw) ∘ₖ returnLaw := potential_unfold _ _
    _ = _ := by rw [← hEq]

theorem pairedOccupation_first_hit_split :
    pairedOccupation = beforeRegeneration + pairedOccupation ∘ₖ hitOrReturn := by
  classical
  ext z B hB
  rw [add_apply, Measure.add_apply, beforeRegeneration, Kernel.piecewise_apply,
    Kernel.comp_apply' _ _ _ hB, hitOrReturn, Kernel.piecewise_apply]
  by_cases hz : z ∈ returnSet
  · simp only [hz, ite_eq_left, zero_apply, Kernel.id_apply]
    rw [lintegral_dirac' z (pairedOccupation.measurable_coe hB)]
    simp
  · simp only [hz]
    have h := congrArg (fun K : Kernel OddCost CostState => K z B) pairedOccupation_unfold_cycles
    rwa [add_apply, Measure.add_apply, Kernel.comp_apply' _ _ _ hB] at h

noncomputable def evenEmbeddingKernel : Kernel EvenState CostState :=
  Kernel.deterministic (fun s : EvenState => (.inl s, 0)) (measurable_inl.prodMk measurable_const)

theorem firstOdd_intertwines :
    oddEmbeddingKernel ∘ₖ firstOdd = costKernel ∘ₖ evenEmbeddingKernel := by
  rw [oddEmbeddingKernel, evenEmbeddingKernel, Kernel.deterministic_comp_eq_map,
    Kernel.comp_deterministic_eq_comap]
  ext s : 1
  rw [Kernel.map_apply _ embedOdd_measurable, Kernel.comap_apply]
  exact firstOdd_full_draw s

theorem fullOccupation_eq_potential : fullOccupation = potential costKernel costKernel := by
  unfold fullOccupation potential
  apply congrArg Kernel.sum
  funext n
  exact pow_succ' costKernel n

theorem fullOccupation_unfold : fullOccupation = costKernel + fullOccupation ∘ₖ costKernel := by
  rw [fullOccupation_eq_potential]
  exact potential_unfold _ _

theorem fullOccupation_odd_kernel : fullOccupation ∘ₖ oddEmbeddingKernel = pairedOccupation := by
  rw [oddEmbeddingKernel, Kernel.comp_deterministic_eq_comap]
  ext z : 1
  rw [Kernel.comap_apply]
  exact (pairedOccupation_eq_full z).symm

theorem fullOccupation_even_first_draw :
    fullOccupation ∘ₖ evenEmbeddingKernel = firstOdd.map embedOdd + pairedOccupation ∘ₖ firstOdd := by
  have hfull := congrArg (fun K : Kernel CostState CostState => K ∘ₖ evenEmbeddingKernel) fullOccupation_unfold
  rw [Kernel.comp_add_left, Kernel.comp_assoc, ← firstOdd_intertwines,
    ← Kernel.comp_assoc, fullOccupation_odd_kernel] at hfull
  have hfirst : oddEmbeddingKernel ∘ₖ firstOdd = firstOdd.map embedOdd := by
    rw [oddEmbeddingKernel, Kernel.deterministic_comp_eq_map]
  rwa [hfirst] at hfull

theorem initial_occupation_decomposition :
    fullOccupation ∘ₖ evenEmbeddingKernel = initialOccupation + pairedOccupation ∘ₖ delayedRegeneration := by
  rw [fullOccupation_even_first_draw]
  have h := congrArg (fun K : Kernel OddCost CostState => K ∘ₖ firstOdd) pairedOccupation_first_hit_split
  rw [Kernel.comp_add_left, Kernel.comp_assoc] at h
  rw [h, ← add_assoc]
  rfl

theorem initial_occupation_decomposition_apply (s : EvenState) :
    fullOccupation (.inl s, 0) = initialOccupation s + (pairedOccupation ∘ₖ delayedRegeneration) s := by
  have h := congrArg (fun K : Kernel EvenState CostState => K s) initial_occupation_decomposition
  rw [evenEmbeddingKernel, Kernel.comp_deterministic_eq_comap, Kernel.comap_apply, add_apply] at h
  exact h

end NumberTheoryLean.InitialOccupation

end

section

namespace NumberTheoryLean.FullOccupationCovariance

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Topology
open TransitionKernels FinitePathMeasures PairedCostProcess PairedCostGrouping
open RegenerationTails CostReturnLaw CycleResponse AdmissibleCycleTests
open OccupationDecomposition OccupationRegeneration SignedCycleOccupation InitialOccupation

instance fullOccupation_isSFiniteKernel : IsSFiniteKernel fullOccupation := by
  rw [fullOccupation_eq_potential]
  infer_instance

theorem shifts_commute_fullOccupation (a : ℝ) :
    shiftFullKernel a ∘ₖ fullOccupation = fullOccupation ∘ₖ shiftFullKernel a := by
  rw [fullOccupation, Kernel.comp_sum_right, Kernel.comp_sum_left]
  apply congrArg Kernel.sum
  funext n
  exact ((shiftFull_commutes a).pow_right (n + 1)).eq

theorem fullOccupation_translation (z : CostState) (a : ℝ) :
    (fullOccupation z).map (shiftFullCost a) = fullOccupation (shiftFullCost a z) := by
  have h := shifts_commute_fullOccupation a
  rw [shiftFullKernel, Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap] at h
  have hz := congrArg (fun K : Kernel CostState CostState => K z) h
  rwa [Kernel.map_apply _ (shiftFullCost_measurable a), Kernel.comap_apply] at hz

theorem fullOccupation_regeneration (s : OddState) (hs : s.1 ≤ 3) (T : ℝ) :
    fullOccupation (embedOdd (s, T)) = fullOccupation (embedOdd (regenerationState, T)) := by
  have hk : costKernel (embedOdd (s, T)) = costKernel (embedOdd (regenerationState, T)) :=
    costKernel_regeneration s hs T
  ext B hB
  rw [fullOccupation, Kernel.sum_apply' _ _ hB, Kernel.sum_apply' _ _ hB]
  apply tsum_congr
  intro n
  have hp : costKernel ^ (n + 1) = (costKernel ^ n) ∘ₖ costKernel := pow_succ _ _
  rw [hp, Kernel.comp_apply, Kernel.comp_apply, hk]

theorem fullOccupation_regeneration_law (z : OddCost) (hz : z ∈ returnSet) :
    fullOccupation (embedOdd z) =
      (fullOccupation (embedOdd (regenerationState, 0))).map (shiftFullCost z.2) := by
  rw [fullOccupation_regeneration z.1 hz z.2, fullOccupation_translation]
  have heq : shiftFullCost z.2 (embedOdd (regenerationState, 0)) = embedOdd (regenerationState, z.2) := by
    simp [shiftFullCost, embedOdd]
  rw [heq]

noncomputable def fullResponse (F : Test) (v : ℝ) : ℝ :=
  ∫ y : CostState, F (v - y.2, y.1) ∂fullOccupation (embedOdd (regenerationState, 0))

theorem fullResponse_measurable {F : Test} (hF : Measurable F) : Measurable (fullResponse F) := by
  exact ((hF.comp ((measurable_fst.sub (measurable_snd.comp measurable_snd)).prodMk
    (measurable_fst.comp measurable_snd))).stronglyMeasurable.integral_prod_right').measurable

theorem fullResponse_uniform_bound {F : Test} (hF : Measurable F) (hB : HasCompactBound F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v, ‖fullResponse F v‖ ≤ C :=
  fullOccupation_test_uniform_bound hF hB

theorem fullResponse_limit {F : Test} (hF : Admissible F) :
    Tendsto (fullResponse F) atTop (𝓝 ((∫ u : ℝ, response F u) / (∫ G : ℝ, G ∂cycleCostLaw))) :=
  fullOccupation_regeneration_limit hF

theorem fullOccupation_regeneration_integral (z : OddCost) (hz : z ∈ returnSet)
    {F : Test} (hF : Measurable F) (v : ℝ) :
    (∫ y : CostState, F (v - y.2, y.1) ∂pairedOccupation z) = fullResponse F (v - z.2) := by
  rw [pairedOccupation_eq_full, fullOccupation_regeneration_law z hz,
    integral_map (shiftFullCost_measurable z.2).aemeasurable (shiftedTest_measurable hF v).aestronglyMeasurable]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  change F (v - (y.2 + z.2), y.1) = F ((v - z.2) - y.2, y.1)
  rw [show v - (y.2 + z.2) = (v - z.2) - y.2 by ring]

theorem fullOccupation_regeneration_integrable (z : OddCost) (hz : z ∈ returnSet)
    {F : Test} (hF : Measurable F) (hB : HasCompactBound F) (v : ℝ) :
    Integrable (fun y : CostState => F (v - y.2, y.1)) (pairedOccupation z) := by
  rw [pairedOccupation_eq_full, fullOccupation_regeneration_law z hz]
  apply (integrable_map_measure (shiftedTest_measurable hF v).aestronglyMeasurable
    (shiftFullCost_measurable z.2).aemeasurable).mpr
  have h := fullOccupation_test_integrable hF hB (v - z.2)
  convert! h using 1
  funext y
  change F (v - (y.2 + z.2), y.1) = F ((v - z.2) - y.2, y.1)
  rw [show v - (y.2 + z.2) = (v - z.2) - y.2 by ring]

end NumberTheoryLean.FullOccupationCovariance

end

section

namespace NumberTheoryLean.InitialOccupationMoments

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open TransitionKernels FinitePathMeasures PairedCostProcess PairedCostGrouping
open CostReturnLaw CycleOccupation CycleResponse AdmissibleCycleTests PairedDrift
open InitialOddDraw InitialRegeneration InitialOccupation UniformCycleMoments

theorem occupation_cost_monotone (z : OddCost) : ∀ᵐ y ∂occupationKernel z, z.2 ≤ y.2 := by
  rw [occupationKernel, Kernel.sum_apply, Measure.ae_sum_iff]
  intro n
  exact (visitBlock_age_bounds n z).mono (fun _ hy => hy.1)

theorem beforeRegeneration_cost_monotone (z : OddCost) : ∀ᵐ y ∂beforeRegeneration z, z.2 ≤ y.2 := by
  classical
  rw [beforeRegeneration, Kernel.piecewise_apply]
  split_ifs
  · simp
  · exact occupation_cost_monotone z

theorem initialOccupation_cost_nonneg (s : EvenState) : ∀ᵐ y ∂initialOccupation s, 0 ≤ y.2 := by
  rw [initialOccupation, add_apply, ae_add_measure_iff]
  constructor
  · rw [Kernel.map_apply _ embedOdd_measurable]
    apply (ae_map_iff embedOdd_measurable.aemeasurable (measurableSet_le measurable_const measurable_snd)).mpr
    exact (firstOdd_cost_bounds s).mono (fun _ h => h.1)
  · apply Kernel.ae_comp_of_ae_ae (measurableSet_le measurable_const measurable_snd)
    filter_upwards [firstOdd_cost_bounds s] with z hz
    filter_upwards [beforeRegeneration_cost_monotone z] with y hy
    exact le_trans hz.1 hy

theorem initialOccupation_uniform_exponential (S : ℝ) : ∃ η B : ℝ,
    0 < η ∧ 0 ≤ B ∧ ∀ s : EvenState, s.1 ≤ S →
      (∫⁻ y, ENNReal.ofReal (Real.exp (η * y.2)) ∂initialOccupation s) ≤ ENNReal.ofReal B := by
  classical
  obtain ⟨η, C, D, hη, hC, hD, hb⟩ := occupation_increment_uniform_exponential
  have hpoint : ∀ z : OddCost,
      ENNReal.ofReal (Real.exp (η * z.2)) +
        (∫⁻ y, ENNReal.ofReal (Real.exp (η * y.2)) ∂beforeRegeneration z) ≤
        ENNReal.ofReal (C + 1) * ENNReal.ofReal (Real.exp (η * z.2) * (V z.1 + (D + 1))) := by
    intro z
    have he : (∫⁻ y, ENNReal.ofReal (Real.exp (η * y.2)) ∂beforeRegeneration z) ≤
        ENNReal.ofReal (Real.exp (η * z.2)) * ENNReal.ofReal (C * (V z.1 + D)) := by
      rw [beforeRegeneration, Kernel.piecewise_apply]
      split_ifs
      · simp
      · rw [exponential_total_eq _ η z.2]
        exact mul_le_mul le_rfl (hb z) zero_le zero_le
    calc
      _ ≤ ENNReal.ofReal (Real.exp (η * z.2)) +
          ENNReal.ofReal (Real.exp (η * z.2)) * ENNReal.ofReal (C * (V z.1 + D)) := add_le_add le_rfl he
      _ ≤ _ := by
        have hV := V_one_le z.1
        have hterm : 0 ≤ C * (V z.1 + D) := mul_nonneg hC (by linarith)
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
          ← ENNReal.ofReal_add (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le hterm),
          ← ENNReal.ofReal_mul (by linarith : 0 ≤ C + 1)]
        apply ENNReal.ofReal_le_ofReal
        have hw : 1 + C * (V z.1 + D) ≤ (C + 1) * (V z.1 + (D + 1)) := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hw (Real.exp_pos (η * z.2)).le]
  obtain ⟨B, hB, hfirst⟩ := firstOdd_weighted_exponential S η (D + 1) hη.le (by linarith)
  refine ⟨η, (C + 1) * B, hη, mul_nonneg (by linarith) hB, ?_⟩
  intro s hs
  have hExp : Measurable (fun y : CostState => ENNReal.ofReal (Real.exp (η * y.2))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul measurable_snd))
  rw [initialOccupation, add_apply, lintegral_add_measure,
    Kernel.map_apply _ embedOdd_measurable, lintegral_map hExp embedOdd_measurable,
    Kernel.lintegral_comp _ _ _ hExp]
  change (∫⁻ z, ENNReal.ofReal (Real.exp (η * z.2)) ∂firstOdd s) +
    (∫⁻ z, ∫⁻ y, ENNReal.ofReal (Real.exp (η * y.2)) ∂beforeRegeneration z ∂firstOdd s) ≤ _
  rw [← lintegral_add_left (f := fun z : OddCost => ENNReal.ofReal (Real.exp (η * z.2)))
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul measurable_snd)))]
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal (C + 1) * ENNReal.ofReal (Real.exp (η * z.2) * (V z.1 + (D + 1))) ∂firstOdd s :=
      lintegral_mono hpoint
    _ = ENNReal.ofReal (C + 1) *
        (∫⁻ z, ENNReal.ofReal (Real.exp (η * z.2) * (V z.1 + (D + 1))) ∂firstOdd s) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (C + 1) * ENNReal.ofReal B := mul_le_mul le_rfl (hfirst s hs) zero_le zero_le
    _ = _ := (ENNReal.ofReal_mul (by linarith : 0 ≤ C + 1)).symm

instance initialOccupation_isFiniteMeasure (s : EvenState) : IsFiniteMeasure (initialOccupation s) := by
  obtain ⟨η, B, hη, hB, hb⟩ := initialOccupation_uniform_exponential s.1
  constructor
  apply lt_of_le_of_lt (show initialOccupation s univ ≤ ∫⁻ y, ENNReal.ofReal (Real.exp (η * y.2)) ∂initialOccupation s from ?_)
    (lt_of_le_of_lt (hb s le_rfl) ENNReal.ofReal_lt_top)
  calc
    _ = ∫⁻ _y, (1 : ℝ≥0∞) ∂initialOccupation s := by simp
    _ ≤ _ := by
      apply lintegral_mono_ae
      filter_upwards [initialOccupation_cost_nonneg s] with y hy
      exact ENNReal.one_le_ofReal.mpr (Real.one_le_exp (mul_nonneg hη.le hy))

theorem initialOccupation_test_decay {F : Test} (_hF : Measurable F) (hB : HasCompactBound F) (S : ℝ) :
    ∃ η B : ℝ, 0 < η ∧ 0 ≤ B ∧ ∀ s : EvenState, s.1 ≤ S → ∀ v : ℝ,
      ‖∫ y : CostState, F (v - y.2, y.1) ∂initialOccupation s‖ ≤ B * Real.exp (-η * v) := by
  obtain ⟨C, M, hC, hM, hbF, hsF⟩ := hB
  obtain ⟨η, B, hη, hB, hb⟩ := initialOccupation_uniform_exponential S
  refine ⟨η, C * B * Real.exp (η * M), hη, by positivity, ?_⟩
  intro s hs v
  have hEi : Integrable (fun y : CostState => Real.exp (η * y.2)) (initialOccupation s) := by
    refine ⟨(Real.measurable_exp.comp (measurable_const.mul measurable_snd)).aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y : CostState => (Real.exp_pos (η * y.2)).le)).mpr
      (lt_of_le_of_lt (hb s hs) ENNReal.ofReal_lt_top)
  have hEB : (∫ y : CostState, Real.exp (η * y.2) ∂initialOccupation s) ≤ B := by
    apply (ENNReal.ofReal_le_ofReal_iff hB).mp
    rw [ofReal_integral_eq_lintegral_ofReal hEi (Eventually.of_forall fun y => (Real.exp_pos _).le)]
    exact hb s hs
  have hpoint : ∀ y : CostState, ‖F (v - y.2, y.1)‖ ≤
      C * Real.exp (-η * (v - M)) * Real.exp (η * y.2) := by
    intro y
    by_cases hy : M < |v - y.2|
    · rw [hsF _ hy, norm_zero]
      positivity
    · have hlow : v - M ≤ y.2 := by have h := (abs_le.mp (le_of_not_gt hy)).2; linarith
      have hExp : 1 ≤ Real.exp (-η * (v - M)) * Real.exp (η * y.2) := by
        rw [← Real.exp_add]
        apply Real.one_le_exp
        nlinarith
      exact le_trans (hbF _) (by nlinarith [mul_le_mul_of_nonneg_left hExp hC])
  calc
    _ ≤ ∫ y : CostState, C * Real.exp (-η * (v - M)) * Real.exp (η * y.2) ∂initialOccupation s :=
      norm_integral_le_of_norm_le (hEi.const_mul _) (Eventually.of_forall hpoint)
    _ = C * Real.exp (-η * (v - M)) * (∫ y : CostState, Real.exp (η * y.2) ∂initialOccupation s) := integral_const_mul _ _
    _ ≤ C * Real.exp (-η * (v - M)) * B := mul_le_mul_of_nonneg_left hEB (by positivity)
    _ = _ := by
      rw [show -η * (v - M) = η * M + -η * v by ring, Real.exp_add]
      ring

end NumberTheoryLean.InitialOccupationMoments

end

section

namespace NumberTheoryLean.UniformDelayedLimit

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open TransitionKernels CostReturnLaw CycleResponse AdmissibleCycleTests
open InitialRegeneration FullOccupationCovariance

theorem exponential_integrable_of_bound {μ : Measure ℝ} {η B : ℝ} (hB : 0 ≤ B)
    (hb : (∫⁻ T, ENNReal.ofReal (Real.exp (η * T)) ∂μ) ≤ ENNReal.ofReal B) :
    Integrable (fun T : ℝ => Real.exp (η * T)) μ ∧ (∫ T, Real.exp (η * T) ∂μ) ≤ B := by
  have hi : Integrable (fun T : ℝ => Real.exp (η * T)) μ := by
    refine ⟨(Real.measurable_exp.comp (measurable_const.mul measurable_id)).aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun T : ℝ => (Real.exp_pos (η * T)).le)).mpr
      (lt_of_le_of_lt hb ENNReal.ofReal_lt_top)
  refine ⟨hi, (ENNReal.ofReal_le_ofReal_iff hB).mp ?_⟩
  rwa [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun T => (Real.exp_pos _).le)]

theorem uniform_shift_limit {ι : Type*} (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (I : Set ι) {η B K L : ℝ}
    (hη : 0 < η) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hmoment : ∀ i ∈ I, (∫⁻ T, ENNReal.ofReal (Real.exp (η * T)) ∂μ i) ≤ ENNReal.ofReal B)
    {R : ℝ → ℝ} (hR : Measurable R) (hbound : ∀ u, ‖R u‖ ≤ K)
    (hlim : Tendsto R atTop (𝓝 L)) :
    ∀ ε : ℝ, 0 < ε → ∃ V : ℝ, ∀ v : ℝ, V ≤ v → ∀ i ∈ I,
      ‖(∫ T, R (v - T) ∂μ i) - L‖ < ε := by
  intro ε hε
  let D := K + ‖L‖ + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hExp : Tendsto (fun M : ℝ => Real.exp (-η * M)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq, neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (Tendsto.const_mul_atTop hη tendsto_id)
  have hTail : Tendsto (fun M : ℝ => (D * B) * Real.exp (-η * M)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hExp.const_mul (D * B)
  obtain ⟨M, hM⟩ := ((tendsto_order.mp hTail).2 (ε / 2) (by positivity)).exists
  have hNorm : Tendsto (fun u : ℝ => ‖R u - L‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (hlim.sub_const L).norm
  obtain ⟨U, hU⟩ := eventually_atTop.mp ((tendsto_order.mp hNorm).2 (ε / 2) (by positivity))
  refine ⟨U + M, ?_⟩
  intro v hv i hi
  obtain ⟨hEi, hEB⟩ := exponential_integrable_of_bound hB (hmoment i hi)
  have hRi : Integrable (fun T : ℝ => R (v - T)) (μ i) :=
    ⟨(hR.comp (measurable_const.sub measurable_id)).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (Eventually.of_forall fun T => hbound _)⟩
  have hpoint : ∀ T : ℝ, ‖R (v - T) - L‖ ≤ ε / 2 + D * Real.exp (-η * M) * Real.exp (η * T) := by
    intro T
    by_cases hT : T ≤ M
    · have hx := (hU (v - T) (by linarith)).le
      exact le_trans hx (le_add_of_nonneg_right (by positivity))
    · have hd : ‖R (v - T) - L‖ ≤ D := by
        have hh := norm_sub_le (R (v - T)) L
        have hbR := hbound (v - T)
        calc
          _ ≤ ‖R (v - T)‖ + ‖L‖ := hh
          _ ≤ K + ‖L‖ := add_le_add hbR le_rfl
          _ ≤ D := by unfold D; linarith
      have he : 1 ≤ Real.exp (-η * M) * Real.exp (η * T) := by
        rw [← Real.exp_add]
        apply Real.one_le_exp
        have hT' : M < T := lt_of_not_ge hT
        nlinarith
      have hd' : D ≤ D * Real.exp (-η * M) * Real.exp (η * T) := by
        nlinarith [mul_le_mul_of_nonneg_left he hD.le]
      exact le_trans hd (le_trans hd' (by linarith))
  calc
    _ = ‖∫ T, (R (v - T) - L) ∂μ i‖ := by rw [integral_sub hRi (integrable_const L)]; simp
    _ ≤ ∫ T, (ε / 2 + D * Real.exp (-η * M) * Real.exp (η * T)) ∂μ i :=
      norm_integral_le_of_norm_le ((integrable_const (ε / 2)).add (hEi.const_mul _)) (Eventually.of_forall hpoint)
    _ = ε / 2 + D * Real.exp (-η * M) * (∫ T, Real.exp (η * T) ∂μ i) := by
      rw [integral_add (integrable_const _) (hEi.const_mul _), integral_const_mul]
      simp
    _ ≤ ε / 2 + D * Real.exp (-η * M) * B :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hEB (by positivity))
    _ < ε := by nlinarith [hM]

theorem actual_delayed_response_limit {F : Test} (hF : Admissible F) (S : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ V : ℝ, ∀ v : ℝ, V ≤ v → ∀ s : EvenState, s.1 ≤ S →
      ‖(∫ T, fullResponse F (v - T) ∂delayedCostLaw s) -
        ((∫ u : ℝ, response F u) / (∫ G : ℝ, G ∂cycleCostLaw))‖ < ε := by
  obtain ⟨η, B, hη, hB, hb⟩ := delayedCostLaw_uniform_exponential S
  obtain ⟨K, hK, hbound⟩ := fullResponse_uniform_bound hF.measurable hF.compactBound
  exact uniform_shift_limit delayedCostLaw {s : EvenState | s.1 ≤ S} hη hB hK
    (fun s hs => hb s hs) (fullResponse_measurable hF.measurable) hbound (fullResponse_limit hF)

end NumberTheoryLean.UniformDelayedLimit

end

section

namespace NumberTheoryLean.EvenStartOccupation

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Topology
open TransitionKernels FinitePathMeasures PairedCostProcess PairedCostGrouping
open CostReturnLaw CycleResponse AdmissibleCycleTests OccupationDecomposition
open InitialRegeneration InitialOccupation InitialOccupationMoments
open FullOccupationCovariance UniformDelayedLimit

theorem compactBound_norm {F : Test} (hB : HasCompactBound F) : HasCompactBound (fun x => ‖F x‖) := by
  obtain ⟨C, M, hC, hM, hb, hs⟩ := hB
  refine ⟨C, M, hC, hM, ?_, ?_⟩
  · intro x
    simpa only [norm_norm] using hb x
  · intro x hx
    change ‖F x‖ = 0
    rw [hs x hx, norm_zero]

theorem initial_test_integrable {F : Test} (hF : Measurable F) (hB : HasCompactBound F)
    (s : EvenState) (v : ℝ) :
    Integrable (fun y : CostState => F (v - y.2, y.1)) (initialOccupation s) := by
  obtain ⟨C, M, hC, hM, hb, hs⟩ := hB
  exact ⟨(shiftedTest_measurable hF v).aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (Eventually.of_forall fun _ => hb _)⟩

theorem future_after_delay_integrable {F : Test} (hF : Measurable F) (hB : HasCompactBound F)
    (s : EvenState) (v : ℝ) :
    Integrable (fun y : CostState => F (v - y.2, y.1)) ((pairedOccupation ∘ₖ delayedRegeneration) s) := by
  have hm : AEStronglyMeasurable (fun y : CostState => F (v - y.2, y.1))
      ((pairedOccupation ∘ₖ delayedRegeneration) s) := (shiftedTest_measurable hF v).aestronglyMeasurable
  apply (integrable_comp_iff hm).mpr
  constructor
  · filter_upwards [delayedRegeneration_ae_regeneration s] with z hz
    exact fullOccupation_regeneration_integrable z hz hF hB v
  · obtain ⟨K, hK, hb⟩ := fullResponse_uniform_bound hF.norm (compactBound_norm hB)
    refine ⟨hm.norm.integral_kernel_comp, HasFiniteIntegral.of_bounded (C := K) ?_⟩
    filter_upwards [delayedRegeneration_ae_regeneration s] with z hz
    rw [fullOccupation_regeneration_integral z hz (F := fun x => ‖F x‖) hF.norm v]
    exact hb (v - z.2)

theorem even_full_test_integrable {F : Test} (hF : Measurable F) (hB : HasCompactBound F)
    (s : EvenState) (v : ℝ) :
    Integrable (fun y : CostState => F (v - y.2, y.1)) (fullOccupation (.inl s, 0)) := by
  rw [initial_occupation_decomposition_apply]
  exact (initial_test_integrable hF hB s v).add_measure (future_after_delay_integrable hF hB s v)

theorem even_full_signed_decomposition {F : Test} (hF : Measurable F) (hB : HasCompactBound F)
    (s : EvenState) (v : ℝ) :
    (∫ y : CostState, F (v - y.2, y.1) ∂fullOccupation (.inl s, 0)) =
      (∫ y : CostState, F (v - y.2, y.1) ∂initialOccupation s) +
        ∫ T, fullResponse F (v - T) ∂delayedCostLaw s := by
  rw [initial_occupation_decomposition_apply,
    integral_add_measure (initial_test_integrable hF hB s v) (future_after_delay_integrable hF hB s v),
    Kernel.integral_comp (future_after_delay_integrable hF hB s v), delayedCostLaw,
    integral_map (f := fun T : ℝ => fullResponse F (v - T)) measurable_snd.aemeasurable
      ((fullResponse_measurable hF).comp (measurable_const.sub measurable_id)).aestronglyMeasurable]
  congr 1
  apply integral_congr_ae
  filter_upwards [delayedRegeneration_ae_regeneration s] with z hz
  exact fullOccupation_regeneration_integral z hz hF v

noncomputable def evenResponse (F : Test) (s : EvenState) (v : ℝ) : ℝ :=
  F (v, .inl s) + ∫ y : CostState, F (v - y.2, y.1) ∂fullOccupation (.inl s, 0)

theorem uniform_even_occupation_limit {F : Test} (hF : Admissible F) (S : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ V : ℝ, ∀ v : ℝ, V ≤ v → ∀ s : EvenState, s.1 ≤ S →
      ‖evenResponse F s v - ((∫ u : ℝ, response F u) / (∫ G : ℝ, G ∂cycleCostLaw))‖ < ε := by
  obtain ⟨C, M, hC, hM, hb, hsupp⟩ := hF.compactBound
  obtain ⟨η, B, hη, hB, hinit⟩ := initialOccupation_test_decay hF.measurable hF.compactBound S
  have hExp : Tendsto (fun v : ℝ => B * Real.exp (-η * v)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp (Tendsto.const_mul_atTop hη tendsto_id)
    simpa only [Function.comp_def, id_eq, neg_mul, mul_zero] using h.const_mul B
  intro ε hε
  obtain ⟨V₁, hV₁⟩ := eventually_atTop.mp ((tendsto_order.mp hExp).2 (ε / 2) (by positivity))
  obtain ⟨V₂, hV₂⟩ := actual_delayed_response_limit hF S (ε / 2) (by positivity)
  refine ⟨max (max V₁ V₂) (M + 1), ?_⟩
  intro v hv s hs
  have hv₁ : V₁ ≤ v := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hv
  have hv₂ : V₂ ≤ v := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hv
  have hvM : M + 1 ≤ v := le_trans (le_max_right _ _) hv
  have hz : F (v, .inl s) = 0 := hsupp _ (by change M < |v|; linarith [le_abs_self v])
  rw [evenResponse, hz, zero_add, even_full_signed_decomposition hF.measurable hF.compactBound]
  let L := (∫ u : ℝ, response F u) / (∫ G : ℝ, G ∂cycleCostLaw)
  have ha : ‖∫ y : CostState, F (v - y.2, y.1) ∂initialOccupation s‖ < ε / 2 :=
    lt_of_le_of_lt (hinit s hs v) (hV₁ v hv₁)
  have hd := hV₂ v hv₂ s hs
  have heq : (∫ y : CostState, F (v - y.2, y.1) ∂initialOccupation s) +
      (∫ T, fullResponse F (v - T) ∂delayedCostLaw s) - L =
      (∫ y : CostState, F (v - y.2, y.1) ∂initialOccupation s) +
        ((∫ T, fullResponse F (v - T) ∂delayedCostLaw s) - L) := by ring
  change ‖_ + _ - L‖ < ε
  rw [heq]
  exact lt_of_le_of_lt (norm_add_le _ _) (by linarith)

theorem source_start_occupation_limit {F : Test} (hF : Admissible F) :
    ∀ ε : ℝ, 0 < ε → ∃ V : ℝ, ∀ v : ℝ, V ≤ v → ∀ s : EvenState,
      (199 / 100 : ℝ) ≤ s.1 → s.1 ≤ 23 / 10 →
      ‖evenResponse F s v - ((∫ u : ℝ, response F u) / (∫ G : ℝ, G ∂cycleCostLaw))‖ < ε := by
  intro ε hε
  obtain ⟨V, hV⟩ := uniform_even_occupation_limit hF (23 / 10) ε hε
  exact ⟨V, fun v hv s _ hs => hV v hv s hs⟩

end NumberTheoryLean.EvenStartOccupation

end

section

namespace NumberTheoryLean.NormalizedOccupationLimit

open Filter Set MeasureTheory
open scoped Topology
open FinitePathMeasures CycleResponse AdmissibleCycleTests OccupationConstant
open EvenStartOccupation FullOccupationCovariance
open Erdos970Dependency.InvariantDensities Erdos970Dependency.InvariantCostBound
open Erdos970Dependency.StateKernelInvariance Erdos970Dependency.CycleMeanCost

noncomputable def invariantAverage (F : Test) : ℝ :=
  (∫ s : State, integratedStateTest F s ∂stateMeasure) / costMass

theorem occupation_constant_eq {F : Test} (hF : Measurable F) (hB : HasCompactBound F) :
    ((∫ v : ℝ, response F v) / (∫ G : ℝ, G ∂CostReturnLaw.cycleCostLaw)) = invariantAverage F := by
  rw [(response_integral_eq_invariant hF hB).2, cycle_mean_eq, invariantAverage]
  field_simp [beta_pos.ne', costMass_pos.ne']

theorem normalized_regeneration_occupation_limit {F : Test} (hF : Admissible F) :
    Tendsto (fullResponse F) atTop (𝓝 (invariantAverage F)) := by
  have h := fullResponse_limit hF
  rwa [occupation_constant_eq hF.measurable hF.compactBound] at h

theorem normalized_uniform_even_occupation_limit {F : Test} (hF : Admissible F) (S : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∃ V : ℝ, ∀ v : ℝ, V ≤ v → ∀ s : TransitionKernels.EvenState, s.1 ≤ S →
      ‖evenResponse F s v - invariantAverage F‖ < ε := by
  have h := uniform_even_occupation_limit hF S
  rwa [occupation_constant_eq hF.measurable hF.compactBound] at h

theorem source_compact_occupation_limit {F : Test} (hF : Admissible F) :
    ∀ ε : ℝ, 0 < ε → ∃ V : ℝ, ∀ v : ℝ, V ≤ v → ∀ s : TransitionKernels.EvenState,
      (199 / 100 : ℝ) ≤ s.1 → s.1 ≤ 23 / 10 →
      ‖evenResponse F s v - invariantAverage F‖ < ε := by
  have h := source_start_occupation_limit hF
  rwa [occupation_constant_eq hF.measurable hF.compactBound] at h

end NumberTheoryLean.NormalizedOccupationLimit

end

section

namespace NumberTheoryLean.RegenerationBandBounds

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathMeasures PairedCostGrouping RegenerationTails CostReturnLaw
open CycleOccupation CycleConvolutionLaw OccupationDecomposition OccupationRegeneration
open AbsorptionCutoff.Renewal
open Erdos970Dependency.InvariantDensities Erdos970Dependency.StateKernelInvariance
open Erdos970Dependency.ActualCycleOccupation

instance cycleRenewal_sFinite : SFinite (renewalMeasure cycleCostLaw) := by
  unfold renewalMeasure
  infer_instance

noncomputable def stateBandReward (Q : State → ℝ≥0∞) (v h : ℝ) : CostState → ℝ≥0∞ :=
  (Prod.snd ⁻¹' Icc v (v + h)).indicator (fun y => Q y.1)

theorem sub_mem_band_iff (v T h : ℝ) : v - T ∈ Icc (-h) 0 ↔ T ∈ Icc v (v + h) := by
  simp only [mem_Icc]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem regeneration_band_identity {Q : State → ℝ≥0∞} (hQ : Measurable Q) (v h : ℝ) :
    (∫⁻ y, stateBandReward Q v h y ∂fullOccupation (embedOdd (regenerationState, 0))) =
      ∫⁻ y : CostState, Q y.1 * renewalMeasure cycleCostLaw (Icc (v - y.2) (v + h - y.2)) ∂occupationMeasure := by
  classical
  let F : ℝ × State → ℝ≥0∞ := (Prod.fst ⁻¹' Icc (-h) 0).indicator (fun x => Q x.2)
  have hF : Measurable F := (hQ.comp measurable_snd).indicator (measurable_fst measurableSet_Icc)
  have heq : stateBandReward Q v h = fun y : CostState => F (v - y.2, y.1) := by
    funext y
    simp only [stateBandReward, F, indicator_apply, mem_preimage, sub_mem_band_iff]
  rw [heq, fullOccupation_positive_convolution hF, ← lintegral_sum_measure, actualArrival_sum_eq_renewal]
  change (∫⁻ T : ℝ, ∫⁻ y : CostState, F (v - T - y.2, y.1) ∂occupationMeasure ∂renewalMeasure cycleCostLaw) = _
  have hjoint : Measurable (Function.uncurry (fun T : ℝ => fun y : CostState => F (v - T - y.2, y.1))) :=
    hF.comp (((measurable_const.sub measurable_fst).sub (measurable_snd.comp measurable_snd)).prodMk
      (measurable_fst.comp measurable_snd))
  rw [lintegral_lintegral_swap hjoint.aemeasurable]
  apply lintegral_congr
  intro y
  have hinner : (fun T : ℝ => F (v - T - y.2, y.1)) =
      (Icc (v - y.2) (v + h - y.2)).indicator (fun _ : ℝ => Q y.1) := by
    funext T
    have hiff : v - T - y.2 ∈ Icc (-h) 0 ↔ T ∈ Icc (v - y.2) (v + h - y.2) := by
      simp only [mem_Icc]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
    simp only [F, indicator_apply, mem_preimage]
    simp only [hiff]
  rw [hinner, lintegral_indicator measurableSet_Icc, lintegral_const]
  simp

theorem regeneration_uniform_band (h : ℝ) : ∃ C : ℝ≥0∞, C < ∞ ∧
    ∀ Q : State → ℝ≥0∞, Measurable Q → ∀ v : ℝ,
      (∫⁻ y, stateBandReward Q v h y ∂fullOccupation (embedOdd (regenerationState, 0))) ≤
        C * ∫⁻ s : State, Q s ∂stateMeasure := by
  obtain ⟨B, hB⟩ := CycleRenewalInputs.cycle_renewal_cell_bound h
  let C := ENNReal.ofReal B * (ENNReal.ofReal beta)⁻¹
  have hβ : ENNReal.ofReal beta ≠ 0 := (ENNReal.ofReal_pos.mpr beta_pos).ne'
  have hC : C < ∞ := lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.mpr hβ))
  refine ⟨C, hC, ?_⟩
  intro Q hQ v
  rw [regeneration_band_identity hQ v h]
  calc
    _ ≤ ∫⁻ y : CostState, Q y.1 * ENNReal.ofReal B ∂occupationMeasure := by
      apply lintegral_mono
      intro y
      apply mul_le_mul le_rfl _ zero_le zero_le
      have hb := hB (v - y.2)
      rwa [show (v - y.2) + h = v + h - y.2 by ring] at hb
    _ = (∫⁻ y : CostState, Q y.1 ∂occupationMeasure) * ENNReal.ofReal B :=
      lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ = C * ∫⁻ s : State, Q s ∂stateMeasure := by
      rw [lintegral_state_occupation hQ]
      dsimp [C]
      ring

end NumberTheoryLean.RegenerationBandBounds

end

end Erdos970

end OAI
