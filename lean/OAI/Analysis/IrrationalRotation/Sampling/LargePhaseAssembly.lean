import Mathlib
import OAI.Analysis.IrrationalRotation.Model.PhaseFailure
import OAI.Analysis.IrrationalRotation.Sampling.PhaseFailureSummability
import OAI.Analysis.IrrationalRotation.Sampling.IntegerPhaseWindow
import OAI.Analysis.IrrationalRotation.Product.IndependentMissBounds
import OAI.Analysis.IrrationalRotation.Product.IndependentAngles
import OAI.Analysis.IrrationalRotation.Analysis.ModuloIntervalMeasure
import OAI.Analysis.IrrationalRotation.Sampling.PhaseRanges
import Mathlib.Probability.Independence.InfinitePi

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace Invariant233.ProductPhases

theorem not_mem_largePhaseFailure_iff {ι : Type*} (J : Finset ι)
    {N : ℝ} (hN : 0 < N) (θ : ι → ℝ) :
    θ ∉ largePhaseFailure J N ↔ largePhaseCondition J N θ := by
  simp only [largePhaseFailure, Set.mem_ofPred_eq, not_exists, not_and,
    not_lt, largePhaseCondition, mem_largePhaseTimes hN]
  constructor
  · intro h k hlo hhi
    exact h k ⟨hlo, hhi⟩
  · intro h k hk
    exact h k hk.1 hk.2

theorem measure_largePhaseFailure_le {ι : Type*}
    (μ : Measure (ι → ℝ)) (J : Finset ι) (N : ℝ) (hm : 100 ≤ (J.card : ℝ))
    (hind : ∀ k : ℤ, iIndepSet
      (fun i => {θ : ι → ℝ | 1 - Int.fract ((k : ℝ) * θ i) ∉
        Set.Icc ((J.card : ℝ) ^ (-19 / 20 : ℝ))
          (1 - (J.card : ℝ) ^ (-19 / 20 : ℝ))}) μ)
    (hmiss : ∀ k ∈ largePhaseTimes N ((J.card : ℝ) ^ ((4 / 5 : ℝ) * J.card)),
      ∀ i ∈ J, μ {θ : ι → ℝ | 1 - Int.fract ((k : ℝ) * θ i) ∉
        Set.Icc ((J.card : ℝ) ^ (-19 / 20 : ℝ))
          (1 - (J.card : ℝ) ^ (-19 / 20 : ℝ))} ≤
        ENNReal.ofReal (10 * (J.card : ℝ) ^ (-19 / 20 : ℝ))) :
    μ (largePhaseFailure J N) ≤ ENNReal.ofReal (failureBound J.card) := by
  classical
  let m : ℝ := J.card
  let b : ℝ := m ^ (-19 / 20 : ℝ)
  let R : ℝ := m ^ ((4 / 5 : ℝ) * m)
  let q : ℝ := (19 / 20 : ℝ) * m
  let times := largePhaseTimes N R
  let E : ℤ → ι → Set (ι → ℝ) := fun k i =>
    {θ | 1 - Int.fract ((k : ℝ) * θ i) ∉ Set.Icc b (1 - b)}
  have hm0 : 0 ≤ m := by dsimp [m]; positivity
  have hb : 0 ≤ b := Real.rpow_nonneg hm0 _
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hp : ENNReal.ofReal (10 * b) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (ten_mul_phaseWidth_le_one hm)
  have hsub : largePhaseFailure J N ⊆
      {θ | ∃ k ∈ times, ∃ t : Finset ι,
        t ⊆ J ∧ q ≤ (t.card : ℝ) ∧ ∀ i ∈ t, θ ∈ E k i} := by
    intro θ hθ
    obtain ⟨k, hk, hsmall⟩ := hθ
    obtain ⟨t, ht, hcard, htmiss⟩ :=
      Invariant233.exists_many_misses_of_few_successes J
        (fun i => 1 - Int.fract ((k : ℝ) * θ i) ∈ Set.Icc b (1 - b)) hsmall
    exact ⟨k, hk, t, ht, hcard.le, htmiss⟩
  have hprob := Invariant233.measure_exists_many_independent_events_le μ E J times
    (fun k _ => hind k) hp hmiss q
  have hnum : (times.card : ℝ) *
      ((2 : ℝ) ^ J.card * (10 * b) ^ q) ≤ failureBound m := by
    calc
      (times.card : ℝ) * ((2 : ℝ) ^ J.card * (10 * b) ^ q) ≤
          (2 * R) * ((2 : ℝ) ^ J.card * (10 * b) ^ q) :=
        mul_le_mul_of_nonneg_right (card_largePhaseTimes_le (Real.rpow_nonneg hm0 _))
          (by positivity)
      _ = failureBound m := by
        dsimp [failureBound, R, b, q, m]
        rw [Real.rpow_natCast]
        ring
  calc
    μ (largePhaseFailure J N) ≤ μ {θ | ∃ k ∈ times, ∃ t : Finset ι,
      t ⊆ J ∧ q ≤ (t.card : ℝ) ∧ ∀ i ∈ t, θ ∈ E k i} := measure_mono hsub
    _ ≤ (times.card : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ J.card *
      ENNReal.ofReal (10 * b) ^ q) := hprob
    _ = ENNReal.ofReal ((times.card : ℝ) * ((2 : ℝ) ^ J.card * (10 * b) ^ q)) := by
      rw [ENNReal.ofReal_mul (p := (times.card : ℝ)) (Nat.cast_nonneg _),
        ENNReal.ofReal_mul (p := (2 : ℝ) ^ J.card) (by positivity),
        ENNReal.ofReal_pow (by norm_num),
        ENNReal.ofReal_rpow_of_nonneg (by positivity) hq]
      simp
    _ ≤ ENNReal.ofReal (failureBound m) := ENNReal.ofReal_le_ofReal hnum

theorem iIndepSet_phaseMiss_infinitePi {ι : Type*} (ν : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (b : ℝ) (k : ℤ) :
    iIndepSet (fun i => {θ : ι → ℝ | 1 - Int.fract ((k : ℝ) * θ i) ∉
      Set.Icc b (1 - b)}) (Measure.infinitePi ν) := by
  have hA : MeasurableSet {x : ℝ | 1 - Int.fract ((k : ℝ) * x) ∉
      Set.Icc b (1 - b)} := by
    exact ((measurable_const.sub (measurable_const.mul measurable_id).fract)
      measurableSet_Icc).compl
  have hm : ∀ i : ι, MeasurableSet {θ : ι → ℝ |
      1 - Int.fract ((k : ℝ) * θ i) ∉ Set.Icc b (1 - b)} :=
    fun i => hA.preimage (measurable_pi_apply i)
  apply (iIndepSet_iff_meas_biInter hm).mpr
  intro S
  have hi : iIndepFun (fun i (θ : ι → ℝ) => θ i) (Measure.infinitePi ν) :=
    iIndepFun_infinitePi (X := fun _ (x : ℝ) => x) (fun _ => measurable_id)
  exact hi.measure_inter_preimage_eq_mul S (fun _ _ => hA)

theorem infinitePi_phaseMiss_eq {ι : Type*} (ν : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (b : ℝ) (k : ℤ) (i : ι) :
    (Measure.infinitePi ν) {θ : ι → ℝ |
      1 - Int.fract ((k : ℝ) * θ i) ∉ Set.Icc b (1 - b)} =
      ν i {x : ℝ | 1 - Int.fract ((k : ℝ) * x) ∉ Set.Icc b (1 - b)} := by
  have hA : MeasurableSet {x : ℝ | 1 - Int.fract ((k : ℝ) * x) ∉
      Set.Icc b (1 - b)} := by
    exact ((measurable_const.sub (measurable_const.mul measurable_id).fract)
      measurableSet_Icc).compl
  simpa only [Measure.infinitePi_map_eval, Set.preimage_ofPred_eq] using
    (Measure.map_apply (μ := Measure.infinitePi ν)
      (f := fun θ : ι → ℝ => θ i) (measurable_pi_apply i) hA).symm

theorem ae_largePhaseCondition_of_miss_bounds {ι : Type*}
    (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ]
    (J : ℕ → Finset ι) (N : ℕ → ℝ)
    (hN : ∀ j, 0 < N j) (hgrowth : ∀ j, 2 ^ j ≤ (J j).card)
    (hind : ∀ (j : ℕ) (k : ℤ), iIndepSet
      (fun i => {θ : ι → ℝ | 1 - Int.fract ((k : ℝ) * θ i) ∉
        Set.Icc (((J j).card : ℝ) ^ (-19 / 20 : ℝ))
          (1 - ((J j).card : ℝ) ^ (-19 / 20 : ℝ))}) μ)
    (hmiss : ∀ᶠ j in atTop,
      ∀ k ∈ largePhaseTimes (N j) (((J j).card : ℝ) ^ ((4 / 5 : ℝ) * (J j).card)),
      ∀ i ∈ J j, μ {θ : ι → ℝ | 1 - Int.fract ((k : ℝ) * θ i) ∉
        Set.Icc (((J j).card : ℝ) ^ (-19 / 20 : ℝ))
          (1 - ((J j).card : ℝ) ^ (-19 / 20 : ℝ))} ≤
        ENNReal.ofReal (10 * ((J j).card : ℝ) ^ (-19 / 20 : ℝ))) :
    ∀ᵐ θ ∂μ, ∀ᶠ j in atTop, largePhaseCondition (J j) (N j) θ := by
  have hreal : ∀ j : ℕ, (2 : ℝ) ^ j ≤ ((J j).card : ℝ) := by
    intro j
    exact_mod_cast hgrowth j
  have hindex : ∀ j : ℕ, (j : ℝ) ≤ ((J j).card : ℝ) := by
    intro j
    exact_mod_cast (le_trans (Nat.lt_two_pow_self (n := j)).le (hgrowth j))
  have htop : Tendsto (fun j => ((J j).card : ℝ)) atTop atTop :=
    tendsto_atTop_mono hindex tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ j in atTop, (100 : ℝ) ≤ (J j).card :=
    htop.eventually_ge_atTop 100
  have hbad : ∀ᶠ j in atTop, μ (largePhaseFailure (J j) (N j)) ≤
      ENNReal.ofReal (failureBound (J j).card) := by
    filter_upwards [hlarge, hmiss] with j hj hm
    exact measure_largePhaseFailure_le μ (J j) (N j) hj (hind j) hm
  have hbc := ae_eventually_notMem_of_phase_bound μ
    (fun j => largePhaseFailure (J j) (N j)) hreal hbad
  filter_upwards [hbc] with θ hθ
  filter_upwards [hθ] with j hj
  exact (not_mem_largePhaseFailure_iff (J j) (hN j) θ).mp hj

theorem uniformProduct_ae_largePhaseCondition {ι : Type*}
    (S : ι → ℝ) (hS : ∀ i, 0 < S i)
    (J : ℕ → Finset ι) (N : ℕ → ℝ) (hN : ∀ j, 0 < N j)
    (hgrowth : ∀ j, 2 ^ j ≤ (J j).card)
    (hblock : ∀ j, ∀ i ∈ J j, S i = N j) :
    ∀ᵐ θ ∂Measure.infinitePi
      (fun i => ProbabilityTheory.cond volume (Set.Icc (1 / S i) (2 / S i))),
      ∀ᶠ j in atTop, largePhaseCondition (J j) (N j) θ := by
  let ν : ι → Measure ℝ := fun i =>
    ProbabilityTheory.cond volume (Set.Icc (1 / S i) (2 / S i))
  let (i : ι) : IsProbabilityMeasure (ν i) :=
    InvariantProjection.IndependentAngles.intervalLaw_isProbabilityMeasure
      (div_lt_div_of_pos_right (by norm_num) (hS i))
  apply ae_largePhaseCondition_of_miss_bounds (Measure.infinitePi ν) J N hN hgrowth
  · intro j k
    exact iIndepSet_phaseMiss_infinitePi ν _ k
  · apply Filter.Eventually.of_forall
    intro j k hk i hi
    rw [infinitePi_phaseMiss_eq ν _ k i]
    apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top (ν i) _) (by positivity)).mpr
    change (ProbabilityTheory.cond volume (Set.Icc (1 / S i) (2 / S i))).real
      {x : ℝ | 1 - Int.fract ((k : ℝ) * x) ∉
        Set.Icc (((J j).card : ℝ) ^ (-19 / 20 : ℝ))
          (1 - ((J j).card : ℝ) ^ (-19 / 20 : ℝ))} ≤ _
    rw [hblock j i hi]
    exact Invariant233.ModuloIntervalMeasure.uniform_angle_threshold_miss_le
      (hN j) ((mem_largePhaseTimes (hN j)).mp hk).1 (by positivity)

theorem exists_summable_independent_largePhases {ι : Type*} [Countable ι]
    (S : ι → ℝ) (hS : ∀ i, 0 < S i) (hsum : Summable (fun i => 1 / S i))
    (J : ℕ → Finset ι) (N : ℕ → ℝ) (hN : ∀ j, 0 < N j)
    (hgrowth : ∀ j, 2 ^ j ≤ (J j).card)
    (hblock : ∀ j, ∀ i ∈ J j, S i = N j) :
    ∃ θ : ι → ℝ,
      (∀ i, θ i ∈ Set.Icc (1 / S i) (2 / S i)) ∧ Summable θ ∧
      (∑' i, θ i) ≤ 2 * (∑' i, 1 / S i) ∧
      LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ) ∧
      (∀ᶠ j in atTop, largePhaseCondition (J j) (N j) θ) := by
  exact InvariantProjection.IndependentAngles.exists_prescribed_summable_independent_and
    S hS hsum (uniformProduct_ae_largePhaseCondition S hS J N hN hgrowth hblock)

theorem smallPhaseCondition_of_bounds {ι : Type*} (J : Finset ι)
    {K G : ℝ} (hJ : 0 < J.card) (hK : 0 < K) (hG : 0 < G)
    (θ : ι → ℝ)
    (hθ : ∀ i ∈ J, θ i ∈ Set.Icc (1 / ((J.card : ℝ) * K))
      (2 / ((J.card : ℝ) * K))) :
    smallPhaseCondition J K G θ := by
  intro k hklo hkhi i hi
  exact Invariant233.phase_small_window
    (by exact_mod_cast hJ) hK hG (hθ i hi).1 (hθ i hi).2 hklo hkhi

theorem uniformProduct_ae_phaseRanges {ι : Type*} [Countable ι]
    (S : ι → ℝ) (hS : ∀ i, 0 < S i)
    (J : ℕ → Finset ι) (K G : ℕ → ℝ)
    (hK : ∀ j, 0 < K j) (hG : ∀ j, 0 < G j)
    (hgrowth : ∀ j, 2 ^ j ≤ (J j).card)
    (hblock : ∀ j, ∀ i ∈ J j, S i = ((J j).card : ℝ) * K j) :
    ∀ᵐ θ ∂Measure.infinitePi
      (fun i => ProbabilityTheory.cond volume (Set.Icc (1 / S i) (2 / S i))),
      (∀ j, smallPhaseCondition (J j) (K j) (G j) θ) ∧
      (∀ᶠ j in atTop, largePhaseCondition (J j) (((J j).card : ℝ) * K j) θ) := by
  have hJ : ∀ j, 0 < (J j).card := fun j =>
    lt_of_lt_of_le (by positivity : 0 < 2 ^ j) (hgrowth j)
  have hN : ∀ j, 0 < ((J j).card : ℝ) * K j := fun j =>
    mul_pos (by exact_mod_cast hJ j) (hK j)
  have hlarge := uniformProduct_ae_largePhaseCondition S hS J
    (fun j => ((J j).card : ℝ) * K j) hN hgrowth hblock
  have hbounds := InvariantProjection.IndependentAngles.intervalProduct_ae_bounds_linearIndependent
    (fun i => 1 / S i) (fun i => 2 / S i)
    (fun i => div_lt_div_of_pos_right (by norm_num) (hS i))
  filter_upwards [hlarge, hbounds] with θ hθlarge hθbounds
  refine ⟨?_, hθlarge⟩
  intro j
  apply smallPhaseCondition_of_bounds (J j) (hJ j) (hK j) (hG j) θ
  intro i hi
  simpa only [hblock j i hi] using hθbounds.1 i

theorem exists_summable_independent_phaseRanges {ι : Type*} [Countable ι]
    (S : ι → ℝ) (hS : ∀ i, 0 < S i) (hsum : Summable (fun i => 1 / S i))
    (J : ℕ → Finset ι) (K G : ℕ → ℝ)
    (hK : ∀ j, 0 < K j) (hG : ∀ j, 0 < G j)
    (hgrowth : ∀ j, 2 ^ j ≤ (J j).card)
    (hblock : ∀ j, ∀ i ∈ J j, S i = ((J j).card : ℝ) * K j) :
    ∃ θ : ι → ℝ,
      (∀ i, θ i ∈ Set.Icc (1 / S i) (2 / S i)) ∧ Summable θ ∧
      (∑' i, θ i) ≤ 2 * (∑' i, 1 / S i) ∧
      LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ) ∧
      (∀ j, smallPhaseCondition (J j) (K j) (G j) θ) ∧
      (∀ᶠ j in atTop, largePhaseCondition (J j) (((J j).card : ℝ) * K j) θ) := by
  exact InvariantProjection.IndependentAngles.exists_prescribed_summable_independent_and
    S hS hsum (uniformProduct_ae_phaseRanges S hS J K G hK hG hgrowth hblock)

end Invariant233.ProductPhases

end OAI
