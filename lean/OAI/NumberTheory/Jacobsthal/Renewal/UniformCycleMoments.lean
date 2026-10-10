import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Moments.IntegrableExpMul
import OAI.NumberTheory.Jacobsthal.Renewal.OccupationAge

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.OccupationBoundaries

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures KernelDensityBridge
open PairedCostProcess CostReturnLaw CycleOccupation MinorizingCostRegularity

 theorem stateRatio_pos (s : State) : 0 < stateRatio s := by
  cases s with
  | inl s => change 0 < s.1; linarith [s.2]
  | inr s => change 0 < s.1; linarith [s.2]

theorem stateKernel_ratio_null (s : State) {B : Set ℝ} (hB : MeasurableSet B)
    (hnull : volume B = 0) : stateKernel s (stateRatio ⁻¹' B) = 0 := by
  rw [← Measure.map_apply stateRatio_measurable hB]
  cases s with
  | inl s => rw [stateKernel_even_ratio, evenKernel_apply, Measure.restrict_eq_zero.mpr hnull, lintegral_zero_measure]
  | inr s => rw [stateKernel_odd_ratio, oddKernel_apply, Measure.restrict_eq_zero.mpr hnull, lintegral_zero_measure]

theorem costKernel_level_null (h : ℝ → ℝ) (hh : Measurable h)
    (hinj : Set.InjOn (fun t => cost t + h t) (Ioi 0)) (z : CostState) (c : ℝ) :
    costKernel z {y | y.2 + h (stateRatio y.1) = c} = 0 := by
  have hA : MeasurableSet {t : ℝ | 0 < t ∧ z.2 + cost t + h t = c} :=
    measurableSet_Ioi.inter (measurableSet_eq_fun ((measurable_const.add cost_measurable).add hh) measurable_const)
  have hnull : volume {t : ℝ | 0 < t ∧ z.2 + cost t + h t = c} = 0 := by
    apply Set.Subsingleton.measure_zero
    intro t ht u hu
    exact hinj ht.1 hu.1 (by linarith [ht.2, hu.2])
  have hB : MeasurableSet {y : CostState | y.2 + h (stateRatio y.1) = c} :=
    measurableSet_eq_fun (measurable_snd.add (hh.comp (stateRatio_measurable.comp measurable_fst))) measurable_const
  rw [costKernel_apply z hB]
  convert! stateKernel_ratio_null z.1 hA hnull using 2
  ext s
  simp only [mem_ofPred_eq, mem_preimage, stateRatio_pos s, true_and]

theorem occupation_null_of_transition_null {B : Set CostState} (hB : MeasurableSet B)
    (hnull : ∀ z : CostState, costKernel z B = 0) : occupationMeasure B = 0 := by
  have hp : ∀ z : OddCost, pairVisits z B = 0 := by
    intro z
    rw [pairVisits_full_steps, Measure.add_apply, hnull]
    have heq : costKernel ^ 2 = costKernel ∘ₖ costKernel := by rw [pow_two]; rfl
    rw [heq, Kernel.comp_apply' _ _ _ hB]
    simp only [hnull, lintegral_zero, add_zero]
  rw [occupationMeasure, occupationKernel, Kernel.sum_apply' _ _ hB]
  have hv : ∀ n, visitBlock n (RegenerationTails.regenerationState, 0) B = 0 := by
    intro n
    rw [visitBlock, Kernel.comp_apply' _ _ _ hB]
    simp only [hp, lintegral_zero]
  simp only [hv, tsum_zero]

theorem occupation_level_null (h : ℝ → ℝ) (hh : Measurable h)
    (hinj : Set.InjOn (fun t => cost t + h t) (Ioi 0)) (c : ℝ) :
    occupationMeasure {y | y.2 + h (stateRatio y.1) = c} = 0 := by
  apply occupation_null_of_transition_null
    (measurableSet_eq_fun (measurable_snd.add (hh.comp (stateRatio_measurable.comp measurable_fst))) measurable_const)
  exact fun z => costKernel_level_null h hh hinj z c

theorem occupation_age_level_null (c : ℝ) : occupationMeasure {y | y.2 = c} = 0 := by
  have hinj : Set.InjOn (fun t => cost t + (0 : ℝ)) (Ioi 0) := by
    simpa only [add_zero] using cost_strictAntiOn.injOn
  simpa only [add_zero] using occupation_level_null (fun _ => 0) measurable_const hinj c

theorem cost_add_log {t : ℝ} (ht : 0 < t) : cost t + Real.log t = Real.log (t + 1) := by
  rw [cost, ← Real.log_mul (by positivity : (1 + 1 / t : ℝ) ≠ 0) ht.ne']
  congr 1
  field_simp

theorem occupation_age_log_ratio_level_null (c : ℝ) :
    occupationMeasure {y | y.2 + Real.log (stateRatio y.1) = c} = 0 := by
  apply occupation_level_null _ Real.measurable_log
  intro t ht u hu htu
  change 0 < t at ht
  change 0 < u at hu
  change cost t + Real.log t = cost u + Real.log u at htu
  rw [cost_add_log ht, cost_add_log hu] at htu
  have : t + 1 = u + 1 := (Real.log_injOn_pos (by change 0 < t + 1; linarith) (by change 0 < u + 1; linarith) htu)
  linarith

theorem occupation_arrival_boundary_null {ell : ℝ} (hell : 0 < ell) (v : ℝ) :
    occupationMeasure {y | stateRatio y.1 = Real.exp (v - y.2) / ell} = 0 := by
  apply measure_mono_null (t := {y | y.2 + Real.log (stateRatio y.1) = v - Real.log ell})
  · intro y hy
    have hs := stateRatio_pos y.1
    have h := congrArg Real.log ((eq_div_iff hell.ne').mp hy)
    rw [Real.log_mul hs.ne' hell.ne', Real.log_exp] at h
    change y.2 + Real.log (stateRatio y.1) = v - Real.log ell
    linarith
  · exact occupation_age_log_ratio_level_null _

end NumberTheoryLean.OccupationBoundaries



namespace NumberTheoryLean.CycleConvolutionLaw

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Topology
open PairedCostProcess CostReturnLaw CycleRegeneration CycleRenewalInputs
open AbsorptionCutoff.Renewal

instance returnLaw_pow_isMarkovKernel (n : ℕ) : IsMarkovKernel (returnLaw ^ n) := by
  induction n with
  | zero => change IsMarkovKernel (Kernel.id : Kernel OddCost OddCost); infer_instance
  | succ n ih =>
    rw [pow_succ']
    change IsMarkovKernel (returnLaw ∘ₖ (returnLaw ^ n))
    infer_instance

theorem cumulative_cost_lintegral (n : ℕ) (z : OddCost) (hz : z ∈ returnSet)
    {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ y, H y.2 ∂(returnLaw ^ n) z) = ∫⁻ G, H (z.2 + G) ∂convPow cycleCostLaw n := by
  induction n generalizing z with
  | zero =>
    change (∫⁻ y, H y.2 ∂Measure.dirac z) = _
    rw [lintegral_dirac' z (f := fun y : OddCost => H y.2) (hH.comp measurable_snd), convPow_zero,
      lintegral_dirac' 0 (f := fun G : ℝ => H (z.2 + G)) (hH.comp (measurable_const.add measurable_id)), add_zero]
  | succ n ih =>
    have hp : returnLaw ^ (n + 1) = (returnLaw ^ n) ∘ₖ returnLaw := pow_succ returnLaw n
    rw [hp, Kernel.lintegral_comp _ _ _ (g := fun y : OddCost => H y.2) (hH.comp measurable_snd)]
    let F : ℝ → ℝ≥0∞ := fun t => ∫⁻ G, H (z.2 + t + G) ∂convPow cycleCostLaw n
    have hF : Measurable F := (hH.comp ((measurable_const.add measurable_fst).add measurable_snd)).lintegral_prod_right'
    calc
      _ = ∫⁻ y, F (y.2 - z.2) ∂returnLaw z := by
        apply lintegral_congr_ae
        filter_upwards [returnLaw_ae_regeneration z] with y hy
        rw [ih y hy]
        apply lintegral_congr
        intro G
        congr 1
        ring
      _ = ∫⁻ t, F t ∂cycleCostLaw := cycle_increment_integral z hz hF
      _ = _ := by
        rw [convPow_succ', Measure.lintegral_conv (f := fun G : ℝ => H (z.2 + G))
          (hH.comp (measurable_const.add measurable_id))]
        apply lintegral_congr
        intro t
        apply lintegral_congr
        intro G
        congr 1
        ring

theorem cumulative_cost_law (n : ℕ) (z : OddCost) (hz : z ∈ returnSet) :
    ((returnLaw ^ n) z).map (fun y => y.2 - z.2) = convPow cycleCostLaw n := by
  apply Measure.ext_of_lintegral
  intro H hH
  rw [lintegral_map (g := fun y : OddCost => y.2 - z.2) hH (measurable_snd.sub measurable_const),
    cumulative_cost_lintegral n z hz (H := fun G : ℝ => H (G - z.2))
      (hH.comp (measurable_id.sub measurable_const))]
  apply lintegral_congr
  intro G
  rw [add_sub_cancel_left]

noncomputable def actualArrivalLaw (n : ℕ) : Measure ℝ :=
  ((returnLaw ^ n) (RegenerationTails.regenerationState, 0)).map Prod.snd

theorem actualArrivalLaw_eq_convPow (n : ℕ) : actualArrivalLaw n = convPow cycleCostLaw n := by
  have hz : (RegenerationTails.regenerationState, (0 : ℝ)) ∈ returnSet := by
    change (1 : ℝ) ≤ 3
    norm_num
  have h := cumulative_cost_law n (RegenerationTails.regenerationState, 0) hz
  simp only [sub_zero] at h
  convert! h using 1

theorem actualArrival_sum_eq_renewal : Measure.sum actualArrivalLaw = renewalMeasure cycleCostLaw := by
  unfold renewalMeasure
  apply congrArg Measure.sum
  funext n
  exact actualArrivalLaw_eq_convPow n

theorem actual_cycle_key_renewal {H : ℝ → ℝ} (hH : Continuous H)
    (hDRI : driNorm (fun x => ‖H x‖ₑ) ≠ ∞) :
    Tendsto (fun y : ℝ => ∑' n : ℕ, ∫ s, H (y - s) ∂actualArrivalLaw n)
      atTop (𝓝 ((∫ x : ℝ, H x) / (∫ G : ℝ, G ∂cycleCostLaw))) := by
  simp_rw [actualArrivalLaw_eq_convPow]
  exact cycle_key_renewal hH hDRI

end NumberTheoryLean.CycleConvolutionLaw



namespace NumberTheoryLean.CycleResponse

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathMeasures CycleOccupation
open AbsorptionCutoff.Renewal

abbrev Test := ℝ × State → ℝ

noncomputable def response (F : Test) (v : ℝ) : ℝ :=
  ∫ y : CostState, F (v - y.2, y.1) ∂occupationMeasure

theorem shiftedTest_measurable {F : Test} (hF : Measurable F) (v : ℝ) :
    Measurable (fun y : CostState => F (v - y.2, y.1)) :=
  hF.comp ((measurable_const.sub measurable_snd).prodMk measurable_fst)

theorem shiftedTest_integrable {F : Test} (hF : Measurable F) {C : ℝ}
    (hbound : ∀ x, ‖F x‖ ≤ C) (v : ℝ) :
    Integrable (fun y : CostState => F (v - y.2, y.1)) occupationMeasure :=
  ⟨(shiftedTest_measurable hF v).aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (Eventually.of_forall fun _ => hbound _)⟩

theorem response_bound {F : Test} {C : ℝ} (hbound : ∀ x, ‖F x‖ ≤ C) (v : ℝ) :
    ‖response F v‖ ≤ C * occupationMeasure.real univ :=
  norm_integral_le_of_norm_le_const (Eventually.of_forall fun _ => hbound _)

theorem response_zero_left {F : Test} {a v : ℝ}
    (hsupp : ∀ x, x.1 < a → F x = 0) (hv : v < a) : response F v = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [occupation_age_nonneg] with y hy
  exact hsupp _ (by linarith)

theorem occupation_age_all_moments (n : ℕ) :
    Integrable (fun y : CostState => y.2 ^ n) occupationMeasure := by
  obtain ⟨η, hη, hp⟩ := occupation_exponential_integrable
  have hn : Integrable (fun y : CostState => Real.exp (-η * y.2)) occupationMeasure := by
    refine (integrable_const (1 : ℝ)).mono'
      (Real.measurable_exp.comp (measurable_const.mul measurable_snd)).aestronglyMeasurable ?_
    filter_upwards [occupation_age_nonneg] with y hy
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  exact integrable_pow_of_integrable_exp_mul (X := Prod.snd) hη.ne' hp hn n

theorem response_continuous_of_ae {F : Test} (hF : Measurable F) {C : ℝ}
    (hbound : ∀ x, ‖F x‖ ≤ C)
    (hcont : ∀ v, ∀ᵐ y ∂occupationMeasure, ContinuousAt (fun u => F (u - y.2, y.1)) v) :
    Continuous (response F) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  exact tendsto_integral_filter_of_dominated_convergence (fun _ => C)
    (Eventually.of_forall fun u => (shiftedTest_measurable hF u).aestronglyMeasurable)
    (Eventually.of_forall fun u => Eventually.of_forall fun y => hbound _)
    (integrable_const C) (hcont v)

theorem response_reciprocal_square_bound {F : Test} {C M : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hbound : ∀ x, ‖F x‖ ≤ C)
    (hsupp : ∀ x, M < |x.1| → F x = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v : ℝ, ‖response F v‖ ≤ K * (1 + v ^ 2)⁻¹ := by
  let Q : CostState → ℝ := fun y => C * (1 + 2 * y.2 ^ 2 + 2 * M ^ 2)
  have hQi : Integrable Q occupationMeasure :=
    (((integrable_const (1 : ℝ)).add ((occupation_age_all_moments 2).const_mul 2)).add
      (integrable_const (2 * M ^ 2))).const_mul C
  have hQpos : ∀ y, 0 ≤ Q y := fun y => mul_nonneg hC (by positivity)
  refine ⟨∫ y, Q y ∂occupationMeasure, integral_nonneg hQpos, ?_⟩
  intro v
  have he : (1 + v ^ 2) * ‖response F v‖ ≤ ∫ y, Q y ∂occupationMeasure := by
    have hh : ∀ y : CostState, ‖(1 + v ^ 2) * F (v - y.2, y.1)‖ ≤ Q y := by
      intro y
      by_cases hy : M < |v - y.2|
      · rw [hsupp _ hy, mul_zero, norm_zero]
        exact hQpos y
      · have hu : |v - y.2| ≤ M := le_of_not_gt hy
        have hu2 : (v - y.2) ^ 2 ≤ M ^ 2 := by
          nlinarith [sq_le_sq₀ (abs_nonneg (v - y.2)) hM |>.mpr hu, sq_abs (v - y.2)]
        have hv2 : v ^ 2 ≤ 2 * y.2 ^ 2 + 2 * M ^ 2 := by nlinarith [sq_nonneg (v - 2 * y.2)]
        rw [norm_mul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 + v ^ 2)]
        exact le_trans (mul_le_mul_of_nonneg_left (hbound _) (by positivity))
          (by dsimp [Q]; nlinarith [mul_le_mul_of_nonneg_right hv2 hC])
    have hi := norm_integral_le_of_norm_le hQi (Eventually.of_forall hh)
    rw [integral_const_mul, norm_mul, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 1 + v ^ 2)] at hi
    exact hi
  rw [← div_eq_mul_inv]
  exact (le_div_iff₀ (by positivity : 0 < 1 + v ^ 2)).mpr (by linarith)

theorem driNorm_le_of_reciprocal_square {H : ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ v, ‖H v‖ ≤ K * (1 + v ^ 2)⁻¹) : driNorm (fun v => ‖H v‖ₑ) < ∞ := by
  let p : ℝ → ℝ≥0∞ := fun v => ENNReal.ofReal ((1 + v ^ 2)⁻¹)
  have hcell : ∀ k : ℤ, cellSup (fun v => ‖H v‖ₑ) k ≤ ENNReal.ofReal K * cellSup p k := by
    intro k
    apply iSup₂_le
    intro v hv
    calc
      _ = ENNReal.ofReal ‖H v‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (K * (1 + v ^ 2)⁻¹) := ENNReal.ofReal_le_ofReal (hbound v)
      _ = ENNReal.ofReal K * p v := ENNReal.ofReal_mul hK
      _ ≤ _ := mul_le_mul le_rfl (le_cellSup hv) zero_le zero_le
  calc
    _ ≤ ∑' k : ℤ, ENNReal.ofReal K * cellSup p k := ENNReal.tsum_le_tsum hcell
    _ = ENNReal.ofReal K * driNorm p := by rw [ENNReal.tsum_mul_left]; rfl
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr driNorm_ofReal_inv_one_add_sq_ne_top)

theorem response_driNorm {F : Test} {C M : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hbound : ∀ x, ‖F x‖ ≤ C)
    (hsupp : ∀ x, M < |x.1| → F x = 0) : driNorm (fun v => ‖response F v‖ₑ) ≠ ∞ := by
  obtain ⟨K, hK, hb⟩ := response_reciprocal_square_bound hC hM hbound hsupp
  exact (driNorm_le_of_reciprocal_square hK hb).ne

end NumberTheoryLean.CycleResponse



namespace NumberTheoryLean.AdmissibleCycleTests

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathMeasures CycleOccupation OccupationBoundaries CycleResponse

noncomputable def mask (B : Set (ℝ × State)) (F : Test) : Test := B.indicator F

def HasCompactBound (F : Test) : Prop := ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧
  (∀ x, ‖F x‖ ≤ C) ∧ (∀ x, M < |x.1| → F x = 0)

def ShiftContinuous (F : Test) : Prop :=
  ∀ v : ℝ, ∀ᵐ y ∂occupationMeasure, ContinuousAt (fun u => F (u - y.2, y.1)) v

theorem HasCompactBound.mask {F : Test} (hF : HasCompactBound F) (B : Set (ℝ × State)) :
    HasCompactBound (mask B F) := by
  classical
  obtain ⟨C, M, hC, hM, hb, hs⟩ := hF
  refine ⟨C, M, hC, hM, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ B
    · simpa [AdmissibleCycleTests.mask, hx] using hb x
    · simpa [AdmissibleCycleTests.mask, hx] using hC
  · intro x hx
    by_cases h : x ∈ B <;> simp [AdmissibleCycleTests.mask, h, hs x hx]

theorem HasCompactBound.add {F G : Test} (hF : HasCompactBound F) (hG : HasCompactBound G) :
    HasCompactBound (fun x => F x + G x) := by
  obtain ⟨C, M, hC, hM, hb, hs⟩ := hF
  obtain ⟨D, N, hD, hN, hb', hs'⟩ := hG
  refine ⟨C + D, max M N, add_nonneg hC hD, le_trans hM (le_max_left _ _), ?_, ?_⟩
  · intro x
    exact le_trans (norm_add_le _ _) (add_le_add (hb x) (hb' x))
  · intro x hx
    change F x + G x = 0
    rw [hs x (lt_of_le_of_lt (le_max_left _ _) hx), hs' x (lt_of_le_of_lt (le_max_right _ _) hx), add_zero]

theorem HasCompactBound.scale {F : Test} (hF : HasCompactBound F) (c : ℝ) :
    HasCompactBound (fun x => c * F x) := by
  obtain ⟨C, M, hC, hM, hb, hs⟩ := hF
  refine ⟨‖c‖ * C, M, mul_nonneg (norm_nonneg _) hC, hM, ?_, ?_⟩
  · intro x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _)
  · intro x hx
    change c * F x = 0
    rw [hs x hx, mul_zero]

theorem continuousAt_cut_lt {f q r : ℝ → ℝ} {v : ℝ}
    (hf : ContinuousAt f v) (hq : Continuous q) (hr : Continuous r) (hne : q v ≠ r v) :
    ContinuousAt (fun u => if q u < r u then f u else 0) v := by
  obtain h | h := lt_or_gt_of_ne hne
  · apply hf.congr
    filter_upwards [(isOpen_lt hq hr).mem_nhds h] with u hu
    simp [hu]
  · apply (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) v).congr
    filter_upwards [(isOpen_lt hr hq).mem_nhds h] with u hu
    simp [not_lt_of_ge hu.le]

theorem continuousAt_cut_le {f q r : ℝ → ℝ} {v : ℝ}
    (hf : ContinuousAt f v) (hq : Continuous q) (hr : Continuous r) (hne : q v ≠ r v) :
    ContinuousAt (fun u => if q u ≤ r u then f u else 0) v := by
  obtain h | h := lt_or_gt_of_ne hne
  · apply hf.congr
    filter_upwards [(isOpen_lt hq hr).mem_nhds h] with u hu
    simp [hu.le]
  · apply (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) v).congr
    filter_upwards [(isOpen_lt hr hq).mem_nhds h] with u hu
    simp [not_le_of_gt hu]

theorem ShiftContinuous.upper {F : Test} (hF : ShiftContinuous F) (a : ℝ) :
    ShiftContinuous (mask {x | x.1 ≤ a} F) := by
  intro v
  have hn : ∀ᵐ y ∂occupationMeasure, y.2 ≠ v - a := by
    simpa only [ae_iff, not_not] using occupation_age_level_null (v - a)
  filter_upwards [hF v, hn] with y hy hn
  have hne : v - y.2 ≠ a := by intro h; apply hn; linarith
  exact continuousAt_cut_le hy (continuous_id.sub continuous_const) continuous_const hne

theorem ShiftContinuous.upperOpen {F : Test} (hF : ShiftContinuous F) (a : ℝ) :
    ShiftContinuous (mask {x | x.1 < a} F) := by
  intro v
  have hn : ∀ᵐ y ∂occupationMeasure, y.2 ≠ v - a := by
    simpa only [ae_iff, not_not] using occupation_age_level_null (v - a)
  filter_upwards [hF v, hn] with y hy hn
  have hne : v - y.2 ≠ a := by intro h; apply hn; linarith
  exact continuousAt_cut_lt hy (continuous_id.sub continuous_const) continuous_const hne

theorem ShiftContinuous.state {F : Test} (hF : ShiftContinuous F) (B : Set State) :
    ShiftContinuous (mask (Prod.snd ⁻¹' B) F) := by
  classical
  intro v
  filter_upwards [hF v] with y hy
  by_cases h : y.1 ∈ B
  · have heq : (fun u => mask (Prod.snd ⁻¹' B) F (u - y.2, y.1)) = fun u => F (u - y.2, y.1) := by
      funext u
      simp [AdmissibleCycleTests.mask, h]
    rw [heq]
    exact hy
  · have heq : (fun u => mask (Prod.snd ⁻¹' B) F (u - y.2, y.1)) = fun _ => 0 := by
      funext u
      simp [AdmissibleCycleTests.mask, h]
    rw [heq]
    exact continuousAt_const

theorem ShiftContinuous.arrival {F : Test} (hF : ShiftContinuous F) {ell : ℝ} (hell : 0 < ell) :
    ShiftContinuous (mask {x | stateRatio x.2 < Real.exp x.1 / ell} F) := by
  intro v
  have hn : ∀ᵐ y ∂occupationMeasure, stateRatio y.1 ≠ Real.exp (v - y.2) / ell := by
    simpa only [ae_iff, not_not] using occupation_arrival_boundary_null hell v
  filter_upwards [hF v, hn] with y hy hn
  change ContinuousAt (fun u => if stateRatio y.1 < Real.exp (u - y.2) / ell then F (u - y.2, y.1) else 0) v
  exact continuousAt_cut_lt hy continuous_const
    ((Real.continuous_exp.comp (continuous_id.sub continuous_const)).div_const ell) hn

inductive Admissible : Test → Prop
  | base {F : Test} (hF : Measurable F) (hc : ∀ s : State, Continuous (fun u => F (u, s)))
      (hb : HasCompactBound F) : Admissible F
  | upper {F : Test} (hF : Admissible F) (a : ℝ) : Admissible (mask {x | x.1 ≤ a} F)
  | upperOpen {F : Test} (hF : Admissible F) (a : ℝ) : Admissible (mask {x | x.1 < a} F)
  | state {F : Test} (hF : Admissible F) (B : Set State) (hB : MeasurableSet B) :
      Admissible (mask (Prod.snd ⁻¹' B) F)
  | arrival {F : Test} (hF : Admissible F) (ell : ℝ) (hell : 0 < ell) :
      Admissible (mask {x | stateRatio x.2 < Real.exp x.1 / ell} F)
  | add {F G : Test} (hF : Admissible F) (hG : Admissible G) : Admissible (fun x => F x + G x)
  | scale {F : Test} (hF : Admissible F) (c : ℝ) : Admissible (fun x => c * F x)

theorem Admissible.lower {F : Test} (hF : Admissible F) (a : ℝ) :
    Admissible (mask {x | a ≤ x.1} F) := by
  classical
  convert hF.add ((hF.upperOpen a).scale (-1)) using 1
  funext x
  by_cases h : x.1 < a
  · simp [mask, h, not_le_of_gt h]
  · simp [mask, h, le_of_not_gt h]

theorem Admissible.lowerOpen {F : Test} (hF : Admissible F) (a : ℝ) :
    Admissible (mask {x | a < x.1} F) := by
  classical
  convert hF.add ((hF.upper a).scale (-1)) using 1
  funext x
  by_cases h : x.1 ≤ a
  · simp [mask, h, not_lt_of_ge h]
  · simp [mask, h, lt_of_not_ge h]

theorem Admissible.intervalIcc {F : Test} (hF : Admissible F) (a b : ℝ) :
    Admissible (mask {x | x.1 ∈ Icc a b} F) := by
  classical
  convert (hF.lower a).upper b using 1
  funext x
  by_cases ha : a ≤ x.1 <;> by_cases hb : x.1 ≤ b <;> simp [mask, ha, hb]

theorem Admissible.intervalIco {F : Test} (hF : Admissible F) (a b : ℝ) :
    Admissible (mask {x | x.1 ∈ Ico a b} F) := by
  classical
  convert (hF.lower a).upperOpen b using 1
  funext x
  by_cases ha : a ≤ x.1 <;> by_cases hb : x.1 < b <;> simp [mask, ha, hb]

theorem Admissible.intervalIoc {F : Test} (hF : Admissible F) (a b : ℝ) :
    Admissible (mask {x | x.1 ∈ Ioc a b} F) := by
  classical
  convert (hF.lowerOpen a).upper b using 1
  funext x
  by_cases ha : a < x.1 <;> by_cases hb : x.1 ≤ b <;> simp [mask, ha, hb]

theorem Admissible.intervalIoo {F : Test} (hF : Admissible F) (a b : ℝ) :
    Admissible (mask {x | x.1 ∈ Ioo a b} F) := by
  classical
  convert (hF.lowerOpen a).upperOpen b using 1
  funext x
  by_cases ha : a < x.1 <;> by_cases hb : x.1 < b <;> simp [mask, ha, hb]

theorem Admissible.measurable {F : Test} (hF : Admissible F) : Measurable F := by
  induction hF with
  | base hf _ _ => exact hf
  | upper _ a ih => exact ih.indicator (measurableSet_le measurable_fst measurable_const)
  | upperOpen _ a ih => exact ih.indicator (measurableSet_lt measurable_fst measurable_const)
  | state _ B hB ih => exact ih.indicator (measurable_snd hB)
  | arrival _ ell _ ih =>
    exact ih.indicator (measurableSet_lt (stateRatio_measurable.comp measurable_snd)
      ((Real.measurable_exp.comp measurable_fst).div_const ell))
  | add _ _ ihF ihG => exact ihF.add ihG
  | scale _ c ih => exact measurable_const.mul ih

theorem Admissible.compactBound {F : Test} (hF : Admissible F) : HasCompactBound F := by
  induction hF with
  | base _ _ hb => exact hb
  | upper _ _ ih => exact ih.mask _
  | upperOpen _ _ ih => exact ih.mask _
  | state _ _ _ ih => exact ih.mask _
  | arrival _ _ _ ih => exact ih.mask _
  | add _ _ ihF ihG => exact ihF.add ihG
  | scale _ c ih => exact ih.scale c

theorem Admissible.shiftContinuous {F : Test} (hF : Admissible F) : ShiftContinuous F := by
  induction hF with
  | base _ hc _ =>
    intro v
    exact Eventually.of_forall fun y => ((hc y.1).comp (continuous_id.sub continuous_const)).continuousAt
  | upper _ a ih => exact ih.upper a
  | upperOpen _ a ih => exact ih.upperOpen a
  | state _ B _ ih => exact ih.state B
  | arrival _ _ hell ih => exact ih.arrival hell
  | add _ _ ihF ihG =>
    intro v
    filter_upwards [ihF v, ihG v] with y hyF hyG
    exact hyF.add hyG
  | scale _ c ih =>
    intro v
    filter_upwards [ih v] with y hy
    exact continuousAt_const.mul hy

theorem Admissible.response_continuous {F : Test} (hF : Admissible F) : Continuous (response F) := by
  obtain ⟨C, M, hC, hM, hb, hs⟩ := hF.compactBound
  exact response_continuous_of_ae hF.measurable hb hF.shiftContinuous

theorem Admissible.response_driNorm {F : Test} (hF : Admissible F) :
    AbsorptionCutoff.Renewal.driNorm (fun v => ‖response F v‖ₑ) ≠ ∞ := by
  obtain ⟨C, M, hC, hM, hb, hs⟩ := hF.compactBound
  exact CycleResponse.response_driNorm hC hM hb hs

theorem admissible_cycle_response_renewal {F : Test} (hF : Admissible F) :
    Tendsto (fun v : ℝ => ∑' n : ℕ, ∫ s, response F (v - s) ∂CycleConvolutionLaw.actualArrivalLaw n)
      atTop (𝓝 ((∫ u : ℝ, response F u) / (∫ G : ℝ, G ∂CostReturnLaw.cycleCostLaw))) :=
  CycleConvolutionLaw.actual_cycle_key_renewal hF.response_continuous hF.response_driNorm

end NumberTheoryLean.AdmissibleCycleTests



namespace NumberTheoryLean.OccupationDecomposition

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathMeasures PairedCostProcess PairedCostGrouping
open CostReturnLaw CycleOccupation KernelPotential

noncomputable def pairedOccupation : Kernel OddCost CostState := potential pairVisits pairedCostKernel

instance pairedOccupation_isSFiniteKernel : IsSFiniteKernel pairedOccupation := by
  unfold pairedOccupation
  infer_instance

theorem returnLaw_eq_potential : returnLaw = potential costCaptured costKilled := rfl

theorem occupationKernel_eq_potential : occupationKernel = potential pairVisits costKilled := rfl

theorem pairedOccupation_cycle_decomposition :
    pairedOccupation = Kernel.sum (fun n : ℕ => occupationKernel ∘ₖ (returnLaw ^ n)) := by
  have hsplit : pairedCostKernel = costKilled + costCaptured := by
    rw [add_comm, costCaptured_add_costKilled]
  rw [pairedOccupation, hsplit, first_capture_decomposition,
    ← occupationKernel_eq_potential, ← returnLaw_eq_potential]
  rfl

noncomputable def oddEmbeddingKernel : Kernel OddCost CostState :=
  Kernel.deterministic embedOdd embedOdd_measurable

theorem oddEmbedding_intertwines :
    oddEmbeddingKernel ∘ₖ pairedCostKernel = (costKernel ^ 2) ∘ₖ oddEmbeddingKernel := by
  rw [oddEmbeddingKernel, Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap]
  ext z : 1
  rw [Kernel.map_apply _ embedOdd_measurable, Kernel.comap_apply]
  exact pairedCost_full_grouping z

theorem oddEmbedding_intertwines_pow (n : ℕ) :
    oddEmbeddingKernel ∘ₖ (pairedCostKernel ^ n) = (costKernel ^ (2 * n)) ∘ₖ oddEmbeddingKernel := by
  induction n with
  | zero =>
    have h0 : pairedCostKernel ^ 0 = (Kernel.id : Kernel OddCost OddCost) := rfl
    have h1 : costKernel ^ (2 * 0) = (Kernel.id : Kernel CostState CostState) := rfl
    rw [h0, h1, Kernel.comp_id, Kernel.id_comp]
  | succ n ih =>
    have hp : pairedCostKernel ^ (n + 1) = (pairedCostKernel ^ n) ∘ₖ pairedCostKernel := pow_succ _ _
    rw [hp, ← Kernel.comp_assoc, ih, Kernel.comp_assoc, oddEmbedding_intertwines,
      ← Kernel.comp_assoc, ← Kernel.pow_add]
    congr 2

theorem pairedCost_pow_full_grouping (n : ℕ) (z : OddCost) :
    ((pairedCostKernel ^ n) z).map embedOdd = (costKernel ^ (2 * n)) (embedOdd z) := by
  have h := oddEmbedding_intertwines_pow n
  rw [oddEmbeddingKernel, Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap] at h
  have hz := congrArg (fun K : Kernel OddCost CostState => K z) h
  rwa [Kernel.map_apply _ embedOdd_measurable, Kernel.comap_apply] at hz

theorem pairVisits_as_full_kernel :
    pairVisits = (costKernel + costKernel ^ 2) ∘ₖ oddEmbeddingKernel := by
  rw [oddEmbeddingKernel, Kernel.comp_deterministic_eq_comap]
  ext z : 1
  rw [Kernel.comap_apply, add_apply]
  exact pairVisits_full_steps z

theorem pairedVisits_full_grouping (n : ℕ) (z : OddCost) :
    (pairVisits ∘ₖ (pairedCostKernel ^ n)) z =
      (costKernel ^ (2 * n + 1)) (embedOdd z) + (costKernel ^ (2 * n + 2)) (embedOdd z) := by
  have heq : pairVisits ∘ₖ (pairedCostKernel ^ n) =
      (costKernel ^ (2 * n + 1) + costKernel ^ (2 * n + 2)) ∘ₖ oddEmbeddingKernel := by
    rw [pairVisits_as_full_kernel, Kernel.comp_assoc, oddEmbedding_intertwines_pow,
      ← Kernel.comp_assoc, Kernel.comp_add_left]
    have h1 : costKernel ∘ₖ (costKernel ^ (2 * n)) = costKernel ^ (2 * n + 1) := by
      exact (pow_succ' costKernel (2 * n)).symm
    have h2 : (costKernel ^ 2) ∘ₖ (costKernel ^ (2 * n)) = costKernel ^ (2 * n + 2) := by
      rw [← Kernel.pow_add]
      congr 1
      omega
    rw [h1, h2]
  rw [heq, oddEmbeddingKernel, Kernel.comp_deterministic_eq_comap, Kernel.comap_apply, add_apply]

noncomputable def fullOccupation : Kernel CostState CostState :=
  Kernel.sum (fun n : ℕ => costKernel ^ (n + 1))

theorem pairedOccupation_eq_full (z : OddCost) : pairedOccupation z = fullOccupation (embedOdd z) := by
  ext B hB
  rw [pairedOccupation, potential, Kernel.sum_apply' _ _ hB, fullOccupation, Kernel.sum_apply' _ _ hB]
  simp_rw [pairedVisits_full_grouping, Measure.add_apply]
  rw [ENNReal.tsum_add]
  simpa only [Nat.add_assoc, show (1 : ℕ) + 1 = 2 by rfl] using
    (tsum_even_add_odd (f := fun n : ℕ => (costKernel ^ (n + 1)) (embedOdd z) B)
      ENNReal.summable ENNReal.summable)

theorem fullOccupation_cycle_decomposition (z : OddCost) :
    fullOccupation (embedOdd z) =
      Measure.sum (fun n : ℕ => (occupationKernel ∘ₖ (returnLaw ^ n)) z) := by
  rw [← pairedOccupation_eq_full, pairedOccupation_cycle_decomposition, Kernel.sum_apply]

theorem fullOccupation_cycle_lintegral (z : OddCost) {F : CostState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y, F y ∂fullOccupation (embedOdd z)) =
      ∑' n : ℕ, ∫⁻ w, ∫⁻ y, F y ∂occupationKernel w ∂(returnLaw ^ n) z := by
  rw [fullOccupation_cycle_decomposition, lintegral_sum_measure]
  apply tsum_congr
  intro n
  exact Kernel.lintegral_comp _ _ _ hF

end NumberTheoryLean.OccupationDecomposition



namespace NumberTheoryLean.OccupationRegeneration

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open TransitionKernels FinitePathGeometry FinitePathMeasures PairedCostProcess PairedCostGrouping
open RegenerationTails CostReturnLaw CycleRegeneration CycleOccupation
open OccupationDecomposition CycleResponse CycleConvolutionLaw

def shiftFullCost (a : ℝ) (z : CostState) : CostState := (z.1, z.2 + a)

theorem shiftFullCost_measurable (a : ℝ) : Measurable (shiftFullCost a) :=
  measurable_fst.prodMk (measurable_snd.add measurable_const)

theorem costKernel_translation (z : CostState) (a : ℝ) :
    (costKernel z).map (shiftFullCost a) = costKernel (shiftFullCost a z) := by
  ext B hB
  rw [Measure.map_apply (shiftFullCost_measurable a) hB,
    costKernel_apply _ ((shiftFullCost_measurable a) hB), costKernel_apply _ hB]
  congr 1
  ext s
  change (s, (z.2 + cost (stateRatio s)) + a) ∈ B ↔
    (s, (z.2 + a) + cost (stateRatio s)) ∈ B
  rw [show z.2 + cost (stateRatio s) + a = z.2 + a + cost (stateRatio s) by ring]

noncomputable def shiftFullKernel (a : ℝ) : Kernel CostState CostState :=
  Kernel.deterministic (shiftFullCost a) (shiftFullCost_measurable a)

theorem shiftFull_commutes (a : ℝ) : Commute (shiftFullKernel a) costKernel := by
  change shiftFullKernel a ∘ₖ costKernel = costKernel ∘ₖ shiftFullKernel a
  rw [shiftFullKernel, Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap]
  ext z : 1
  rw [Kernel.map_apply _ (shiftFullCost_measurable a), Kernel.comap_apply]
  exact costKernel_translation z a

theorem costKernel_pow_translation (n : ℕ) (z : CostState) (a : ℝ) :
    ((costKernel ^ n) z).map (shiftFullCost a) = (costKernel ^ n) (shiftFullCost a z) := by
  have h := ((shiftFull_commutes a).pow_right n).eq
  change shiftFullKernel a ∘ₖ (costKernel ^ n) = (costKernel ^ n) ∘ₖ shiftFullKernel a at h
  rw [shiftFullKernel, Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap] at h
  have hz := congrArg (fun K : Kernel CostState CostState => K z) h
  rwa [Kernel.map_apply _ (shiftFullCost_measurable a), Kernel.comap_apply] at hz

theorem pairVisits_translation (z : OddCost) (a : ℝ) :
    (pairVisits z).map (shiftFullCost a) = pairVisits (shiftCost a z) := by
  rw [pairVisits_full_steps, Measure.map_add _ _ (shiftFullCost_measurable a),
    costKernel_translation, costKernel_pow_translation, pairVisits_full_steps]
  rfl

theorem shifts_intertwine_pairVisits (a : ℝ) :
    shiftFullKernel a ∘ₖ pairVisits = pairVisits ∘ₖ shiftKernel a := by
  rw [shiftFullKernel, shiftKernel, Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap]
  ext z : 1
  rw [Kernel.map_apply _ (shiftFullCost_measurable a), Kernel.comap_apply]
  exact pairVisits_translation z a

theorem shifts_intertwine_occupation (a : ℝ) :
    shiftFullKernel a ∘ₖ occupationKernel = occupationKernel ∘ₖ shiftKernel a := by
  rw [occupationKernel, Kernel.comp_sum_right, Kernel.comp_sum_left]
  apply congrArg Kernel.sum
  funext n
  have hQ := ((shift_commutes_killed a).pow_right n).eq
  change shiftKernel a ∘ₖ (costKilled ^ n) = (costKilled ^ n) ∘ₖ shiftKernel a at hQ
  change shiftFullKernel a ∘ₖ (pairVisits ∘ₖ (costKilled ^ n)) =
    (pairVisits ∘ₖ (costKilled ^ n)) ∘ₖ shiftKernel a
  rw [← Kernel.comp_assoc, shifts_intertwine_pairVisits, Kernel.comp_assoc, hQ, ← Kernel.comp_assoc]

theorem occupation_translation (z : OddCost) (a : ℝ) :
    (occupationKernel z).map (shiftFullCost a) = occupationKernel (shiftCost a z) := by
  have h := shifts_intertwine_occupation a
  rw [shiftFullKernel, shiftKernel, Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap] at h
  have hz := congrArg (fun K : Kernel OddCost CostState => K z) h
  rwa [Kernel.map_apply _ (shiftFullCost_measurable a), Kernel.comap_apply] at hz

theorem pairVisits_regeneration (s : OddState) (hs : s.1 ≤ 3) (T : ℝ) :
    pairVisits (s, T) = pairVisits (regenerationState, T) := by
  rw [pairVisits_full_steps, pairVisits_full_steps]
  have hfirst : costKernel (embedOdd (s, T)) = costKernel (embedOdd (regenerationState, T)) :=
    costKernel_regeneration s hs T
  have hpow : costKernel ^ 2 = costKernel ∘ₖ costKernel := by rw [pow_two]; rfl
  rw [hfirst, hpow, Kernel.comp_apply, Kernel.comp_apply, hfirst]

theorem visitBlock_regeneration (n : ℕ) (s : OddState) (hs : s.1 ≤ 3) (T : ℝ) :
    visitBlock n (s, T) = visitBlock n (regenerationState, T) := by
  cases n with
  | zero =>
    change (pairVisits ∘ₖ (Kernel.id : Kernel OddCost OddCost)) (s, T) =
      (pairVisits ∘ₖ (Kernel.id : Kernel OddCost OddCost)) (regenerationState, T)
    rw [Kernel.comp_id]
    exact pairVisits_regeneration s hs T
  | succ n =>
    have hp : costKilled ^ (n + 1) = (costKilled ^ n) ∘ₖ costKilled := pow_succ _ _
    have hq : (costKilled ^ (n + 1)) (s, T) = (costKilled ^ (n + 1)) (regenerationState, T) := by
      rw [hp, Kernel.comp_apply, Kernel.comp_apply, costKilled_regeneration s hs T]
    rw [visitBlock, Kernel.comp_apply, Kernel.comp_apply, hq]

theorem occupation_regeneration (s : OddState) (hs : s.1 ≤ 3) (T : ℝ) :
    occupationKernel (s, T) = occupationKernel (regenerationState, T) := by
  ext B hB
  rw [occupationKernel, Kernel.sum_apply' _ _ hB, Kernel.sum_apply' _ _ hB]
  apply tsum_congr
  intro n
  rw [visitBlock_regeneration n s hs T]

theorem occupation_regeneration_law (z : OddCost) (hz : z ∈ returnSet) :
    occupationKernel z = occupationMeasure.map (shiftFullCost z.2) := by
  rw [occupation_regeneration z.1 hz z.2, occupationMeasure, occupation_translation]
  have heq : shiftCost z.2 (regenerationState, 0) = (regenerationState, z.2) := by simp [shiftCost]
  rw [heq]

noncomputable def positiveResponse (F : ℝ × State → ℝ≥0∞) (v : ℝ) : ℝ≥0∞ :=
  ∫⁻ y : CostState, F (v - y.2, y.1) ∂occupationMeasure

theorem positiveResponse_measurable {F : ℝ × State → ℝ≥0∞} (hF : Measurable F) :
    Measurable (positiveResponse F) := by
  exact (hF.comp ((measurable_fst.sub (measurable_snd.comp measurable_snd)).prodMk
    (measurable_fst.comp measurable_snd))).lintegral_prod_right'

theorem occupation_response_lintegral (z : OddCost) (hz : z ∈ returnSet)
    {F : ℝ × State → ℝ≥0∞} (hF : Measurable F) (v : ℝ) :
    (∫⁻ y : CostState, F (v - y.2, y.1) ∂occupationKernel z) = positiveResponse F (v - z.2) := by
  rw [occupation_regeneration_law z hz, lintegral_map
    (f := fun y : CostState => F (v - y.2, y.1))
    (hF.comp ((measurable_const.sub measurable_snd).prodMk measurable_fst)) (shiftFullCost_measurable z.2)]
  apply lintegral_congr
  intro y
  congr 1
  dsimp [shiftFullCost]
  ext <;> simp only
  ring

theorem occupation_response_integral (z : OddCost) (hz : z ∈ returnSet)
    {F : Test} (hF : Measurable F) (v : ℝ) :
    (∫ y : CostState, F (v - y.2, y.1) ∂occupationKernel z) = response F (v - z.2) := by
  rw [occupation_regeneration_law z hz, integral_map (shiftFullCost_measurable z.2).aemeasurable
    (shiftedTest_measurable hF v).aestronglyMeasurable]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  change F (v - (y.2 + z.2), y.1) = F ((v - z.2) - y.2, y.1)
  rw [show v - (y.2 + z.2) = (v - z.2) - y.2 by ring]

theorem returnLaw_pow_ae_regeneration (n : ℕ) (z : OddCost) (hz : z ∈ returnSet) :
    ∀ᵐ w ∂(returnLaw ^ n) z, w ∈ returnSet := by
  cases n with
  | zero =>
    change ∀ᵐ w ∂Measure.dirac z, w ∈ returnSet
    exact (ae_dirac_iff returnSet_measurable).mpr hz
  | succ n =>
    have hp : returnLaw ^ (n + 1) = returnLaw ∘ₖ (returnLaw ^ n) := pow_succ' _ _
    rw [hp]
    exact Kernel.ae_comp_of_ae_ae returnSet_measurable
      (Eventually.of_forall fun w => returnLaw_ae_regeneration w)

theorem fullOccupation_positive_convolution {F : ℝ × State → ℝ≥0∞}
    (hF : Measurable F) (v : ℝ) :
    (∫⁻ y : CostState, F (v - y.2, y.1) ∂fullOccupation (embedOdd (regenerationState, 0))) =
      ∑' n : ℕ, ∫⁻ s, positiveResponse F (v - s) ∂actualArrivalLaw n := by
  have hz : (regenerationState, (0 : ℝ)) ∈ returnSet := by change (1 : ℝ) ≤ 3; norm_num
  rw [fullOccupation_cycle_lintegral _ (F := fun y : CostState => F (v - y.2, y.1)) (hF.comp ((measurable_const.sub measurable_snd).prodMk measurable_fst))]
  apply tsum_congr
  intro n
  rw [actualArrivalLaw, lintegral_map (f := fun s : ℝ => positiveResponse F (v - s))
    ((positiveResponse_measurable hF).comp (measurable_const.sub measurable_id)) measurable_snd]
  apply lintegral_congr_ae
  filter_upwards [returnLaw_pow_ae_regeneration n (regenerationState, 0) hz] with w hw
  exact occupation_response_lintegral w hw hF v

end NumberTheoryLean.OccupationRegeneration



namespace NumberTheoryLean.SignedCycleOccupation

open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Topology
open FinitePathMeasures PairedCostProcess PairedCostGrouping RegenerationTails
open CostReturnLaw CycleOccupation CycleResponse CycleConvolutionLaw
open AdmissibleCycleTests OccupationDecomposition OccupationRegeneration
open AbsorptionCutoff.Renewal

theorem positiveResponse_norm_eq {F : Test} (hF : Measurable F) {C : ℝ}
    (hbound : ∀ x, ‖F x‖ ≤ C) (v : ℝ) :
    positiveResponse (fun x => ‖F x‖ₑ) v = ‖response (fun x => ‖F x‖) v‖ₑ := by
  have hi : Integrable (fun y : CostState => ‖F (v - y.2, y.1)‖) occupationMeasure :=
    (shiftedTest_integrable hF hbound v).norm
  have hp : 0 ≤ response (fun x => ‖F x‖) v := integral_nonneg (fun y => norm_nonneg _)
  rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hp]
  have h := ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun y => norm_nonneg _)
  simpa only [positiveResponse, response, ofReal_norm] using h.symm

theorem positiveResponse_norm_driNorm {F : Test} (hF : Measurable F) (hB : HasCompactBound F) :
    driNorm (positiveResponse (fun x => ‖F x‖ₑ)) ≠ ∞ := by
  obtain ⟨C, M, hC, hM, hb, hs⟩ := hB
  have heq : positiveResponse (fun x => ‖F x‖ₑ) = fun v => ‖response (fun x => ‖F x‖) v‖ₑ :=
    funext (positiveResponse_norm_eq hF hb)
  rw [heq]
  apply response_driNorm hC hM
  · intro x
    simpa only [norm_norm] using hb x
  · intro x hx
    rw [hs x hx, norm_zero]

theorem fullOccupation_norm_lintegral_bound {F : Test} (hF : Measurable F)
    (hB : HasCompactBound F) : ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ v : ℝ,
      (∫⁻ y : CostState, ‖F (v - y.2, y.1)‖ₑ ∂fullOccupation (embedOdd (regenerationState, 0))) ≤ C := by
  obtain ⟨D, hD⟩ := CycleRenewalInputs.cycle_renewal_cell_bound 1
  let H := positiveResponse (fun x => ‖F x‖ₑ)
  have hH : driNorm H ≠ ∞ := positiveResponse_norm_driNorm hF hB
  refine ⟨ENNReal.ofReal D * driNorm H, ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hH), ?_⟩
  intro v
  rw [fullOccupation_positive_convolution hF.enorm]
  simp_rw [actualArrivalLaw_eq_convPow]
  exact tsum_lintegral_comp_sub_le hD H v

theorem fullOccupation_test_integrable {F : Test} (hF : Measurable F)
    (hB : HasCompactBound F) (v : ℝ) :
    Integrable (fun y : CostState => F (v - y.2, y.1))
      (fullOccupation (embedOdd (regenerationState, 0))) := by
  obtain ⟨C, hC, hb⟩ := fullOccupation_norm_lintegral_bound hF hB
  exact ⟨(shiftedTest_measurable hF v).aestronglyMeasurable, lt_of_le_of_lt (hb v) hC⟩

theorem fullOccupation_test_uniform_bound {F : Test} (hF : Measurable F)
    (hB : HasCompactBound F) : ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ,
      ‖∫ y : CostState, F (v - y.2, y.1) ∂fullOccupation (embedOdd (regenerationState, 0))‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := fullOccupation_norm_lintegral_bound hF hB
  refine ⟨C.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro v
  calc
    _ ≤ (∫⁻ y : CostState, ‖F (v - y.2, y.1)‖ₑ ∂fullOccupation (embedOdd (regenerationState, 0))).toReal :=
      by simpa only [ofReal_norm] using (norm_integral_le_lintegral_norm
        (μ := fullOccupation (embedOdd (regenerationState, 0))) (fun y : CostState => F (v - y.2, y.1)))
    _ ≤ C.toReal := ENNReal.toReal_mono hC.ne (hb v)

theorem fullOccupation_signed_convolution {F : Test} (hF : Admissible F) (v : ℝ) :
    (∫ y : CostState, F (v - y.2, y.1) ∂fullOccupation (embedOdd (regenerationState, 0))) =
      ∑' n : ℕ, ∫ s, response F (v - s) ∂actualArrivalLaw n := by
  have hz : (regenerationState, (0 : ℝ)) ∈ returnSet := by change (1 : ℝ) ≤ 3; norm_num
  have hI := fullOccupation_test_integrable hF.measurable hF.compactBound v
  rw [fullOccupation_cycle_decomposition] at hI ⊢
  rw [integral_sum_measure hI]
  apply tsum_congr
  intro n
  have hn := (integrable_sum_measure_iff.mp hI).1 n
  rw [Kernel.integral_comp hn, actualArrivalLaw, integral_map (f := fun s : ℝ => response F (v - s)) measurable_snd.aemeasurable
    ((hF.response_continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)]
  apply integral_congr_ae
  filter_upwards [returnLaw_pow_ae_regeneration n (regenerationState, 0) hz] with w hw
  exact occupation_response_integral w hw hF.measurable v

theorem fullOccupation_regeneration_limit {F : Test} (hF : Admissible F) :
    Tendsto (fun v : ℝ => ∫ y : CostState, F (v - y.2, y.1)
      ∂fullOccupation (embedOdd (regenerationState, 0))) atTop
      (𝓝 ((∫ u : ℝ, response F u) / (∫ G : ℝ, G ∂cycleCostLaw))) := by
  simpa only [fullOccupation_signed_convolution hF] using admissible_cycle_response_renewal hF

end NumberTheoryLean.SignedCycleOccupation



namespace NumberTheoryLean.CycleResponseFubini

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathMeasures CycleOccupation CycleResponse AdmissibleCycleTests

noncomputable def ageShear (x : CostState × ℝ) : CostState × ℝ := (x.1, x.2 - x.1.2)

theorem ageShear_measurable : Measurable ageShear :=
  measurable_fst.prodMk (measurable_snd.sub (measurable_snd.comp measurable_fst))

theorem ageShear_measurePreserving : MeasurePreserving ageShear
    (occupationMeasure.prod volume) (occupationMeasure.prod volume) := by
  apply MeasurePreserving.skew_product (g := fun y : CostState => fun u : ℝ => u - y.2) (MeasurePreserving.id occupationMeasure)
    (measurable_snd.sub (measurable_snd.comp measurable_fst))
  apply Eventually.of_forall
  intro y
  simpa only [sub_eq_add_neg] using map_add_right_eq_self (volume : Measure ℝ) (-y.2)

theorem unshifted_test_product_integrable {F : Test} (hF : Measurable F)
    (hB : HasCompactBound F) :
    Integrable (fun x : CostState × ℝ => F (x.2, x.1.1)) (occupationMeasure.prod volume) := by
  classical
  obtain ⟨C, M, hC, hM, hb, hs⟩ := hB
  have hi : Integrable ((Icc (-M) M).indicator (fun _ : ℝ => (1 : ℝ))) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const isCompact_Icc.measure_ne_top)
  have hprod := (integrable_const C : Integrable (fun _ : CostState => C) occupationMeasure).mul_prod hi
  refine hprod.mono' (hF.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))).aestronglyMeasurable ?_
  apply Eventually.of_forall
  intro x
  by_cases hx : x.2 ∈ Icc (-M) M
  · simpa only [indicator_of_mem hx, mul_one] using hb (x.2, x.1.1)
  · have habs : M < |x.2| := by
      apply lt_of_not_ge
      intro hu
      exact hx (abs_le.mp hu)
    rw [hs (x.2, x.1.1) habs, norm_zero, indicator_of_notMem hx, mul_zero]

theorem shifted_test_product_integrable {F : Test} (hF : Measurable F)
    (hB : HasCompactBound F) :
    Integrable (fun x : CostState × ℝ => F (x.2 - x.1.2, x.1.1)) (occupationMeasure.prod volume) := by
  exact ageShear_measurePreserving.integrable_comp_of_integrable (unshifted_test_product_integrable hF hB)

theorem response_integrable {F : Test} (hF : Measurable F) (hB : HasCompactBound F) :
    Integrable (response F) volume := by
  exact (shifted_test_product_integrable hF hB).integral_prod_right

theorem integrated_test_occupation_integrable {F : Test} (hF : Measurable F)
    (hB : HasCompactBound F) :
    Integrable (fun y : CostState => ∫ u : ℝ, F (u, y.1)) occupationMeasure :=
  (unshifted_test_product_integrable hF hB).integral_prod_left

theorem integral_response_eq_occupation {F : Test} (hF : Measurable F)
    (hB : HasCompactBound F) :
    (∫ v : ℝ, response F v) = ∫ y : CostState, (∫ u : ℝ, F (u, y.1)) ∂occupationMeasure := by
  calc
    _ = ∫ y : CostState, (∫ u : ℝ, F (u - y.2, y.1)) ∂occupationMeasure :=
      (integral_integral_swap (shifted_test_product_integrable hF hB)).symm
    _ = _ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro y
      exact integral_sub_right_eq_self (fun u : ℝ => F (u, y.1)) y.2

end NumberTheoryLean.CycleResponseFubini



namespace NumberTheoryLean.OccupationConstant

open Set MeasureTheory
open FinitePathMeasures CycleResponse CycleResponseFubini AdmissibleCycleTests
open Erdos970Dependency.InvariantDensities Erdos970Dependency.StateKernelInvariance
open Erdos970Dependency.ActualCycleOccupation

noncomputable def integratedStateTest (F : Test) (s : State) : ℝ := ∫ u : ℝ, F (u, s)

theorem integratedStateTest_measurable {F : Test} (hF : Measurable F) :
    Measurable (integratedStateTest F) := hF.stronglyMeasurable.integral_prod_left'.measurable

theorem response_integral_eq_invariant {F : Test} (hF : Measurable F) (hB : HasCompactBound F) :
    Integrable (integratedStateTest F) stateMeasure ∧
      (∫ v : ℝ, response F v) = (1 / beta) * ∫ s : State, integratedStateTest F s ∂stateMeasure := by
  obtain ⟨hI, hEq⟩ := integral_state_occupation (integratedStateTest_measurable hF)
    (integrated_test_occupation_integrable hF hB)
  refine ⟨hI, ?_⟩
  rw [integral_response_eq_occupation hF hB]
  exact hEq

end NumberTheoryLean.OccupationConstant



namespace NumberTheoryLean.UniformCycleMoments

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open PairedCostProcess CostReturnLaw CycleCostMoments CycleDurationMoments
open PairedDrift PairedHitting PairedBlockContraction CycleOccupation

theorem geometric_exponential_budget {m : ℕ} (hm : 0 < m) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) : ∃ θ C : ℝ, 0 < θ ∧ 0 ≤ C ∧ ∀ W : ℝ, 0 ≤ W →
      (∑' n : ℕ, ENNReal.ofReal (Real.exp (θ * (2 * ((n : ℝ) + 1)))) *
        ENNReal.ofReal (ρ ^ (n / m) * W)) ≤ ENNReal.ofReal (C * W) := by
  let θ := -Real.log ρ / (4 * (m : ℝ))
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hθ : 0 < θ := div_pos (neg_pos.mpr (Real.log_neg hρ hρ1)) (by positivity)
  have hrel : 4 * (m : ℝ) * θ = -Real.log ρ := by dsimp [θ]; field_simp
  let A := Real.exp (-Real.log ρ + 2 * θ)
  let r := Real.exp (-2 * θ)
  have hA : 0 ≤ A := (Real.exp_pos _).le
  have hr : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hsum : Summable (fun n : ℕ => A * r ^ n) := (summable_geometric_of_lt_one hr hr1).mul_left A
  let C := ∑' n : ℕ, A * r ^ n
  have hC : 0 ≤ C := tsum_nonneg (fun n => mul_nonneg hA (pow_nonneg hr n))
  refine ⟨θ, C, hθ, hC, ?_⟩
  intro W hW
  calc
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (A * r ^ n) * ENNReal.ofReal W := by
      apply ENNReal.tsum_le_tsum
      intro n
      have h := weighted_geometric_bound hm hρ hθ hrel n
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (mul_nonneg hA (pow_nonneg hr n))]
      apply ENNReal.ofReal_le_ofReal
      dsimp [A, r]
      nlinarith [mul_le_mul_of_nonneg_right h hW]
    _ = (∑' n : ℕ, ENNReal.ofReal (A * r ^ n)) * ENNReal.ofReal W := ENNReal.tsum_mul_right
    _ = ENNReal.ofReal C * ENNReal.ofReal W := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg hA (pow_nonneg hr n)) hsum]
    _ = _ := (ENNReal.ofReal_mul hC).symm

theorem return_increment_uniform_exponential : ∃ η C D : ℝ,
    0 < η ∧ 0 ≤ C ∧ 0 < D ∧ ∀ z : OddCost,
      (∫⁻ y, ENNReal.ofReal (Real.exp (η * (y.2 - z.2))) ∂returnLaw z) ≤
        ENNReal.ofReal (C * (V z.1 + D)) := by
  obtain ⟨m, hm, ρ, D, hρ, hρ1, hD, hb⟩ := firstReturn_geometric
  obtain ⟨θ, C, hθ, hC, hbudget⟩ := geometric_exponential_budget hm hρ hρ1
  let η := θ / Real.log 3
  have hL : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hη : 0 < η := div_pos hθ hL
  refine ⟨η, C, D, hη, hC, hD, ?_⟩
  intro z
  rw [returnLaw, Kernel.sum_apply, lintegral_sum_measure]
  apply le_trans (ENNReal.tsum_le_tsum ?_) (hbudget (V z.1 + D) (add_nonneg (V_pos z.1).le hD.le))
  intro n
  calc
    _ ≤ ∫⁻ _y, ENNReal.ofReal (Real.exp (θ * (2 * ((n : ℝ) + 1)))) ∂firstReturn n z := by
      apply lintegral_mono_ae
      filter_upwards [firstReturn_cost_upper n z] with y hy
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      calc
        η * (y.2 - z.2) ≤ η * (2 * ((n + 1 : ℕ) : ℝ) * Real.log 3) :=
          mul_le_mul_of_nonneg_left (by linarith) hη.le
        _ = _ := by dsimp [η]; push_cast; field_simp
    _ = ENNReal.ofReal (Real.exp (θ * (2 * ((n : ℝ) + 1)))) * firstReturn n z univ := lintegral_const _
    _ ≤ _ := mul_le_mul le_rfl (hb n z) zero_le zero_le

theorem occupation_increment_uniform_exponential : ∃ η C D : ℝ,
    0 < η ∧ 0 ≤ C ∧ 0 < D ∧ ∀ z : OddCost,
      (∫⁻ y, ENNReal.ofReal (Real.exp (η * (y.2 - z.2))) ∂occupationKernel z) ≤
        ENNReal.ofReal (C * (V z.1 + D)) := by
  obtain ⟨m, hm, ρ, D, hρ, hρ1, hD, hb⟩ := paired_survival_geometric
  obtain ⟨θ, C, hθ, hC, hbudget⟩ := geometric_exponential_budget hm hρ hρ1
  let η := θ / Real.log 3
  have hL : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hη : 0 < η := div_pos hθ hL
  refine ⟨η, 2 * C, D, hη, mul_nonneg (by norm_num) hC, hD, ?_⟩
  intro z
  have hW : 0 ≤ V z.1 + D := add_nonneg (V_pos z.1).le hD.le
  rw [occupationKernel, Kernel.sum_apply, lintegral_sum_measure]
  calc
    _ ≤ ∑' n : ℕ, 2 * (ENNReal.ofReal (Real.exp (θ * (2 * ((n : ℝ) + 1)))) *
        ENNReal.ofReal (ρ ^ (n / m) * (V z.1 + D))) := by
      apply ENNReal.tsum_le_tsum
      intro n
      have hsurv : (costKilled ^ n) z univ ≤ ENNReal.ofReal (ρ ^ (n / m) * (V z.1 + D)) := by
        rw [costKilled_mass]
        exact le_trans (paired_survival_antitone z.1 (Nat.mul_div_le n m)) (hb (n / m) z.1)
      calc
        _ ≤ ∫⁻ _y, ENNReal.ofReal (Real.exp (θ * (2 * ((n : ℝ) + 1)))) ∂visitBlock n z := by
          apply lintegral_mono_ae
          filter_upwards [visitBlock_age_bounds n z] with y hy
          apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_exp.mpr
          calc
            η * (y.2 - z.2) ≤ η * (2 * ((n + 1 : ℕ) : ℝ) * Real.log 3) :=
              mul_le_mul_of_nonneg_left (by linarith [hy.2]) hη.le
            _ = _ := by dsimp [η]; push_cast; field_simp
        _ = ENNReal.ofReal (Real.exp (θ * (2 * ((n : ℝ) + 1)))) * (2 * (costKilled ^ n) z univ) := by
          rw [lintegral_const, visitBlock_mass]
        _ ≤ ENNReal.ofReal (Real.exp (θ * (2 * ((n : ℝ) + 1)))) *
            (2 * ENNReal.ofReal (ρ ^ (n / m) * (V z.1 + D))) :=
          mul_le_mul le_rfl (mul_le_mul le_rfl hsurv zero_le zero_le) zero_le zero_le
        _ = _ := by ring
    _ = 2 * ∑' n : ℕ, ENNReal.ofReal (Real.exp (θ * (2 * ((n : ℝ) + 1)))) *
        ENNReal.ofReal (ρ ^ (n / m) * (V z.1 + D)) := ENNReal.tsum_mul_left
    _ ≤ 2 * ENNReal.ofReal (C * (V z.1 + D)) := mul_le_mul le_rfl (hbudget _ hW) zero_le zero_le
    _ = _ := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring

end NumberTheoryLean.UniformCycleMoments


end Erdos970

end OAI
