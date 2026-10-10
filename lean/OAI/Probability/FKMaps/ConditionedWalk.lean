import OAI.Probability.FKMaps.HeightCoding

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

local instance : MeasurableSpace C(unitInterval, ℝ) := borel _
local instance : BorelSpace C(unitInterval, ℝ) := ⟨rfl⟩

lemma CriticalEvenOffspring.iid_bridge_pos (p : CriticalEvenOffspring) (n : ℕ) :
    0 < (p.iidLaw (2*n+1)).real {d | totalStep d = -1} := by
  rw [← p.bridgePartition_eq_iid, codePartition_cyclic p (by omega)]
  exact mul_pos (by positivity) (codePartition_odd_pos p n)


def CriticalEvenOffspring.bridgeLaw (p : CriticalEvenOffspring) (n : ℕ) :
    Measure (Fin (2*n+1) → ℕ) :=
  cond (p.iidLaw (2*n+1)) {d | totalStep d = -1}


instance (p : CriticalEvenOffspring) (n : ℕ) : IsProbabilityMeasure (p.bridgeLaw n) := by
  apply cond_isProbabilityMeasure
  intro h
  have hp := p.iid_bridge_pos n
  simp only [measureReal_def, h, ENNReal.toReal_zero, lt_self_iff_false] at hp


lemma CriticalEvenOffspring.bridgeLaw_real (p : CriticalEvenOffspring) (n : ℕ)
    (E : Set (Fin (2*n+1) → ℕ)) :
    (p.bridgeLaw n).real E =
      (p.iidLaw (2*n+1)).real {d | d ∈ E ∧ totalStep d = -1} /
        (p.iidLaw (2*n+1)).real {d | totalStep d = -1} := by
  have hs : {d : Fin (2*n+1) → ℕ | totalStep d = -1} ∩ E =
      {d | d ∈ E ∧ totalStep d = -1} := by ext d; exact and_comm
  change ((cond (p.iidLaw (2*n+1)) {d | totalStep d = -1}) E).toReal = _
  rw [cond_apply (by measurability) (p.iidLaw (2*n+1)) E, hs,
    ENNReal.toReal_mul, ENNReal.toReal_inv]
  rw [div_eq_mul_inv, mul_comm]
  rfl


def degreeFrequency {N : ℕ} (d : Fin N → ℕ) (k : ℕ) : ℝ :=
  (∑ i : Fin N, if d i = k then (1:ℝ) else 0) / N


lemma degreeFrequency_nonneg {N : ℕ} (d : Fin N → ℕ) (k : ℕ) :
    0 ≤ degreeFrequency d k := by unfold degreeFrequency; positivity


lemma degreeFrequency_le_one {N : ℕ} (hN : 0 < N) (d : Fin N → ℕ) (k : ℕ) :
    degreeFrequency d k ≤ 1 := by
  rw [degreeFrequency, div_le_one (by positivity : (0:ℝ)<N)]
  calc
    _ ≤ ∑ _i : Fin N, (1:ℝ) := Finset.sum_le_sum (fun _ _ => by split_ifs <;> norm_num)
    _ = _ := by simp


lemma degreeFrequency_integrable {N : ℕ} (hN : 0 < N)
    (μ : Measure (Fin N → ℕ)) [IsFiniteMeasure μ] (k : ℕ) :
    Integrable (fun d => degreeFrequency d k) μ := by
  apply (integrable_const (1:ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
  filter_upwards [] with d
  rw [Real.norm_of_nonneg (degreeFrequency_nonneg d k)]
  exact degreeFrequency_le_one hN d k


lemma degreeFrequency_square_integrable {N : ℕ} (hN : 0 < N)
    (μ : Measure (Fin N → ℕ)) [IsFiniteMeasure μ] (k : ℕ) (c : ℝ) :
    Integrable (fun d => (degreeFrequency d k-c)^2) μ := by
  apply (integrable_const ((1+|c|)^2)).mono' (measurable_of_countable _).aestronglyMeasurable
  filter_upwards [] with d
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have h : |degreeFrequency d k-c| ≤ 1+|c| := by
    calc
      _ ≤ |degreeFrequency d k|+|c| := abs_sub _ _
      _ ≤ _ := by rw [abs_of_nonneg (degreeFrequency_nonneg d k)]; gcongr; exact degreeFrequency_le_one hN d k
  nlinarith [sq_abs (degreeFrequency d k-c), abs_nonneg (degreeFrequency d k-c), abs_nonneg c]


lemma coordinate_indicator_integrable {N : ℕ} (μ : Measure (Fin N → ℕ))
    [IsFiniteMeasure μ] (i : Fin N) (k : ℕ) :
    Integrable (fun d => if d i = k then (1:ℝ) else 0) μ := by
  apply (integrable_const (1:ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
  exact ae_of_all _ (fun d => by split_ifs <;> norm_num)


lemma coordinate_pair_indicator_integrable {N : ℕ} (μ : Measure (Fin N → ℕ))
    [IsFiniteMeasure μ] (i j : Fin N) (k : ℕ) :
    Integrable (fun d => (if d i = k then (1:ℝ) else 0) *
      (if d j = k then (1:ℝ) else 0)) μ := by
  apply (integrable_const (1:ℝ)).mono' (measurable_of_countable _).aestronglyMeasurable
  exact ae_of_all _ (fun d => by split_ifs <;> norm_num)


lemma integral_coordinate_indicator {N : ℕ} (μ : Measure (Fin N → ℕ))
    (i : Fin N) (k : ℕ) :
    (∫ d, if d i = k then (1:ℝ) else 0 ∂μ) = μ.real {d | d i = k} := by
  simpa only [Set.indicator_apply, Pi.one_apply, Set.mem_ofPred_eq] using
    (integral_indicator_one (μ := μ) (s := {d | d i = k}) (by measurability))


lemma integral_coordinate_pair_indicator {N : ℕ} (μ : Measure (Fin N → ℕ))
    (i j : Fin N) (k : ℕ) :
    (∫ d, (if d i = k then (1:ℝ) else 0) * (if d j = k then (1:ℝ) else 0) ∂μ) =
      μ.real {d | d i = k ∧ d j = k} := by
  have heq : (fun d : Fin N → ℕ => (if d i = k then (1:ℝ) else 0) *
      (if d j = k then (1:ℝ) else 0)) = {d | d i = k ∧ d j = k}.indicator 1 := by
    ext d
    by_cases hi : d i = k <;> by_cases hj : d j = k <;> simp [hi,hj]
  rw [heq]
  exact integral_indicator_one (by measurability)


lemma integral_degreeFrequency {N : ℕ} (hN : 0 < N)
    (μ : Measure (Fin N → ℕ)) [IsFiniteMeasure μ] (k : ℕ) {a : ℝ}
    (ha : ∀ i, μ.real {d | d i = k} = a) :
    (∫ d, degreeFrequency d k ∂μ) = a := by
  simp only [degreeFrequency, integral_div, integral_finsetSum _
    (fun i _ => coordinate_indicator_integrable μ i k), integral_coordinate_indicator, ha,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hN.ne')


lemma integral_degreeFrequency_sq {N : ℕ} (hN : 0 < N)
    (μ : Measure (Fin N → ℕ)) [IsFiniteMeasure μ] (k : ℕ) {a b : ℝ}
    (ha : ∀ i, μ.real {d | d i = k} = a)
    (hb : ∀ i j, i ≠ j → μ.real {d | d i = k ∧ d j = k} = b) :
    (∫ d, (degreeFrequency d k)^2 ∂μ) = b + (a-b)/N := by
  have heq (d : Fin N → ℕ) : (degreeFrequency d k)^2 =
      (∑ i : Fin N, ∑ j : Fin N, (if d i = k then (1:ℝ) else 0) *
        (if d j = k then (1:ℝ) else 0)) / (N:ℝ)^2 := by
    rw [degreeFrequency, div_pow, pow_two, Finset.sum_mul]
    simp only [Finset.mul_sum]
  have hint (i : Fin N) : Integrable (fun d : Fin N → ℕ =>
      ∑ j : Fin N, (if d i = k then (1:ℝ) else 0) * (if d j = k then (1:ℝ) else 0)) μ :=
    integrable_finsetSum _ (fun j _ => coordinate_pair_indicator_integrable μ i j k)
  simp only [heq, integral_div, integral_finsetSum _ (fun i _ => hint i),
    integral_finsetSum _ (fun j _ => coordinate_pair_indicator_integrable μ _ j k),
    integral_coordinate_pair_indicator]
  have hm (i j : Fin N) : μ.real {d | d i = k ∧ d j = k} =
      (if j = i then a-b else 0) + b := by
    by_cases h : j=i
    · subst j
      simp [ha]
    · rw [hb i j (Ne.symm h), ite_eq_right h, zero_add]
  simp only [hm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hN' : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  field_simp [hN']
  ring


lemma integral_degreeFrequency_square_error {N : ℕ} (hN : 0 < N)
    (μ : Measure (Fin N → ℕ)) [IsProbabilityMeasure μ] (k : ℕ) {a b : ℝ} (c : ℝ)
    (ha : ∀ i, μ.real {d | d i = k} = a)
    (hb : ∀ i j, i ≠ j → μ.real {d | d i = k ∧ d j = k} = b) :
    (∫ d, (degreeFrequency d k-c)^2 ∂μ) = b + (a-b)/N - 2*c*a + c^2 := by
  have hf := degreeFrequency_integrable hN μ k
  have hsq : Integrable (fun d => (degreeFrequency d k)^2) μ := by
    simpa only [sub_zero] using degreeFrequency_square_integrable hN μ k 0
  have heq (d : Fin N → ℕ) : (degreeFrequency d k-c)^2 =
      (degreeFrequency d k)^2 - 2*c*(degreeFrequency d k) + c^2 := by ring
  simp only [heq]
  have hsub : Integrable (fun d => degreeFrequency d k ^ 2 - 2*c*degreeFrequency d k) μ :=
    hsq.sub (hf.const_mul (2*c))
  rw [integral_add hsub (integrable_const (c^2)),
    integral_sub hsq (hf.const_mul (2*c)), integral_const_mul,
    integral_degreeFrequency hN μ k ha, integral_degreeFrequency_sq hN μ k ha hb]
  simp


lemma degreeFrequency_deviation_bound {N : ℕ} (hN : 0 < N)
    (μ : Measure (Fin N → ℕ)) [IsProbabilityMeasure μ] (k : ℕ) (c : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    μ.real {d | ε < |degreeFrequency d k-c|} ≤
      (∫ d, (degreeFrequency d k-c)^2 ∂μ)/ε^2 := by
  rw [le_div_iff₀ (sq_pos_of_pos hε), mul_comm]
  apply le_trans _ (mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun _ => sq_nonneg _)
    (degreeFrequency_square_integrable hN μ k c) (ε^2))
  apply mul_le_mul_of_nonneg_left (measureReal_mono _) (sq_nonneg _)
  intro d hd
  change ε^2 ≤ (degreeFrequency d k-c)^2
  have hp := hd
  simp only [Set.mem_ofPred_eq] at hp
  nlinarith [sq_abs (degreeFrequency d k-c), abs_nonneg (degreeFrequency d k-c)]


lemma CriticalEvenOffspring.iid_cond_real (p : CriticalEvenOffspring) (N : ℕ)
    (E : Set (Fin N → ℕ)) :
    (cond (p.iidLaw N) {d | totalStep d = -1}).real E =
      (p.iidLaw N).real {d | d ∈ E ∧ totalStep d = -1} /
        (p.iidLaw N).real {d | totalStep d = -1} := by
  have hs : {d : Fin N → ℕ | totalStep d = -1} ∩ E =
      {d | d ∈ E ∧ totalStep d = -1} := by ext d; exact and_comm
  change ((cond (p.iidLaw N) {d | totalStep d = -1}) E).toReal = _
  rw [cond_apply (by measurability) (p.iidLaw N) E, hs,
    ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_mul_inv, mul_comm]
  rfl


def CriticalEvenOffspring.iidSiteProbability (p : CriticalEvenOffspring) (N : ℕ)
    (j : ℤ) : ℝ := (p.iidLaw N).real {d | totalStep d = j}


def CriticalEvenOffspring.singleBridgeProbability (p : CriticalEvenOffspring) (N k : ℕ) : ℝ :=
  (p.iidLaw (N+1)).real {d | d 0 = k ∧ totalStep d = -1} /
    (p.iidLaw (N+1)).real {d | totalStep d = -1}


def CriticalEvenOffspring.bridgeFrequencyDeviation (p : CriticalEvenOffspring)
    (N k : ℕ) (ε : ℝ) : ℝ :=
  (cond (p.iidLaw N) {d | totalStep d = -1}).real
    {d | ε < |degreeFrequency d k - p.mass k|}


theorem CriticalEvenOffspring.bridge_frequency_limit (p : CriticalEvenOffspring)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (p.bridgeLaw n).real
      {d | ε < |degreeFrequency d k - p.mass k|}) atTop (𝓝 0) := by
  apply (tendsto_add_atTop_iff_nat 2).mp
  let μ (n : ℕ) := cond (p.iidLaw (2*n+5)) {d | totalStep d = -1}
  have hμ (n : ℕ) : IsProbabilityMeasure (μ n) := by
    apply cond_isProbabilityMeasure
    intro h
    have hp := p.iid_bridge_pos (n+2)
    change 0 < p.iidSiteProbability (2*(n+2)+1) (-1) at hp
    norm_num only [Nat.mul_add, Nat.reduceMul, Nat.add_assoc, Nat.reduceAdd] at hp
    change 0 < ((p.iidLaw (2*n+5)) {d | totalStep d = -1}).toReal at hp
    simp only [h, ENNReal.toReal_zero, lt_self_iff_false] at hp
  let a (n : ℕ) := (p.iidLaw (2*n+5)).real {d | d 0 = k ∧ totalStep d = -1} /
    (p.iidLaw (2*n+5)).real {d | totalStep d = -1}
  let b (n : ℕ) := (p.iidLaw (2*n+5)).real
      {d | d 0 = k ∧ d ((0 : Fin (2*n+5)).succAbove 0) = k ∧ totalStep d = -1} /
    (p.iidLaw (2*n+5)).real {d | totalStep d = -1}
  have ha : Tendsto a atTop (𝓝 (p.mass k)) := by
    have ha' := (p.bridge_coordinate_limit k).comp (tendsto_add_atTop_nat 1)
    change Tendsto (fun n => p.singleBridgeProbability (2*(n+1)+2) k) atTop
      (𝓝 (p.mass k)) at ha'
    change Tendsto (fun n => p.singleBridgeProbability (2*n+4) k) atTop (𝓝 (p.mass k))
    simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.reduceAdd] using ha' 
  have hb : Tendsto b atTop (𝓝 (p.mass k * p.mass k)) :=
    p.bridge_pair_limit k k (fun _ => 0) (fun _ => 0)
  have hsingle (n : ℕ) (i : Fin (2*n+5)) :
      (μ n).real {d | d i = k} = a n := by
    rw [p.iid_cond_real]
    simp only [Set.mem_ofPred_eq]
    change _ = _ / _
    rw [p.iid_coordinate_site (2*n+4), p.iid_coordinate_site (2*n+4)]
  have hpair (n : ℕ) (i j : Fin (2*n+5)) (hij : i ≠ j) :
      (μ n).real {d | d i = k ∧ d j = k} = b n := by
    obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hij.symm
    rw [p.iid_cond_real]
    simp only [Set.mem_ofPred_eq, and_assoc]
    change _ = _ / _
    rw [p.iid_pair_site (2*n+3), p.iid_pair_site (2*n+3)]
  have hN : Tendsto (fun n : ℕ => (2*n+5 : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right atTop 5
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0:ℝ)<2))
  have ht : Tendsto (fun n => b n + (a n-b n)/(2*n+5) -
      2*p.mass k*a n + p.mass k^2) atTop (𝓝 0) := by
    convert ((hb.add ((ha.sub hb).div_atTop hN)).sub
      (ha.const_mul (2*p.mass k))).add (tendsto_const_nhds (x := p.mass k^2)) using 1
    congr 1
    ring
  have hvar : Tendsto (fun n => ∫ d, (degreeFrequency d k-p.mass k)^2 ∂μ n)
      atTop (𝓝 0) := by
    convert ht using 1
    ext n
    have := hμ n
    rw [integral_degreeFrequency_square_error (by omega) (μ n) k (p.mass k)
      (hsingle n) (hpair n)]
    norm_num
  have hlim : Tendsto (fun n => (μ n).real
      {d | ε < |degreeFrequency d k - p.mass k|}) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => measureReal_nonneg) (fun n => ?_)
      (by simpa using hvar.div_const (ε^2))
    have := hμ n
    exact degreeFrequency_deviation_bound (by omega) (μ n) k (p.mass k) hε
  change Tendsto (fun n => p.bridgeFrequencyDeviation (2*(n+2)+1) k ε) atTop (𝓝 0)
  change Tendsto (fun n => p.bridgeFrequencyDeviation (2*n+5) k ε) atTop (𝓝 0) at hlim
  simpa only [Nat.mul_add, Nat.reduceMul, Nat.add_assoc, Nat.reduceAdd] using hlim


lemma degreeFrequency_rotation {N : ℕ} [NeZero N] (k : ℕ) (m : Fin N)
    (d : Fin N → Fin N) :
    degreeFrequency (fun i => (rotateDegrees m d i).val) k =
      degreeFrequency (fun i => (d i).val) k := by
  unfold degreeFrequency
  congr 1
  exact Equiv.sum_comp (Equiv.addRight m)
    (fun i => if (d i).val = k then (1:ℝ) else 0)


lemma code_frequency_probability_eq_bridge (p : CriticalEvenOffspring)
    (n k : ℕ) (ε : ℝ) :
    codeEventProbability p (2*n+1)
      (fun d => ε < |degreeFrequency (fun i => (d i).val) k-p.mass k|) =
    (p.bridgeLaw n).real {d | ε < |degreeFrequency d k-p.mass k|} := by
  rw [codeEventProbability_eq_bridge p (by omega) _ (by
    intro m d
    rw [degreeFrequency_rotation]), p.bridgePartition_eq_iid,
    p.bridgeEventMass_eq_iid (2*n+1) (fun d => ε < |degreeFrequency d k-p.mass k|),
    p.bridgeLaw_real]
  congr 2
  ext d
  exact and_comm


theorem CriticalEvenOffspring.conditioned_degree_frequencies (p : CriticalEvenOffspring)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => codeEventProbability p (2*n+1)
      (fun d => ε < |degreeFrequency (fun i => (d i).val) k-p.mass k|))
      atTop (𝓝 0) := by
  simpa only [code_frequency_probability_eq_bridge] using p.bridge_frequency_limit k hε


lemma degreeFrequency_abs_integrable {N : ℕ} (hN : 0 < N)
    (μ : Measure (Fin N → ℕ)) [IsFiniteMeasure μ] (k : ℕ) (c : ℝ) :
    Integrable (fun d => |degreeFrequency d k-c|) μ :=
  ((degreeFrequency_integrable hN μ k).sub (integrable_const c)).abs


lemma integral_degreeFrequency_abs_bound {N : ℕ} (hN : 0 < N)
    (μ : Measure (Fin N → ℕ)) [IsProbabilityMeasure μ]
    (k : ℕ) {c : ℝ} (hc : 0 ≤ c) {ε : ℝ} (hε : 0 ≤ ε) :
    (∫ d, |degreeFrequency d k-c| ∂μ) ≤
      ε + (1+c)*μ.real {d | ε < |degreeFrequency d k-c|} := by
  let E : Set (Fin N → ℕ) := {d | ε < |degreeFrequency d k-c|}
  have hind : Integrable (E.indicator (fun _ => (1+c))) μ :=
    (integrable_const (1+c)).indicator (by measurability)
  have hpoint (d : Fin N → ℕ) :
      |degreeFrequency d k-c| ≤ ε + E.indicator (fun _ => (1+c)) d := by
    by_cases hd : d ∈ E
    · rw [Set.indicator_of_mem hd]
      have hf := degreeFrequency_le_one hN d k
      have hf0 := degreeFrequency_nonneg d k
      have hab := abs_sub (degreeFrequency d k) c
      rw [abs_of_nonneg hf0, abs_of_nonneg hc] at hab
      linarith
    · rw [Set.indicator_of_notMem hd, add_zero]
      exact le_of_not_gt hd
  have h := integral_mono (degreeFrequency_abs_integrable hN μ k c)
    ((integrable_const ε).add hind) hpoint
  change (∫ d, |degreeFrequency d k-c| ∂μ) ≤
    ∫ d, ε + E.indicator (fun _ => (1+c)) d ∂μ at h
  rw [integral_add (integrable_const ε) hind, integral_indicator (by measurability),
    setIntegral_const, integral_const] at h
  simpa [E, mul_comm] using h


theorem CriticalEvenOffspring.bridge_frequency_l1_limit (p : CriticalEvenOffspring) (k : ℕ) :
    Tendsto (fun n : ℕ => ∫ d, |degreeFrequency d k-p.mass k| ∂p.bridgeLaw n)
      atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => lt_of_lt_of_le ha (integral_nonneg (fun _ => abs_nonneg _)))
  · intro b hb
    have hhalf : 0 < b/2 := by positivity
    have ht := (p.bridge_frequency_limit k hhalf).const_mul (1+p.mass k)
    simp only [mul_zero] at ht
    filter_upwards [(tendsto_order.1 ht).2 (b/2) hhalf] with n hn
    apply lt_of_le_of_lt (integral_degreeFrequency_abs_bound (by omega) (p.bridgeLaw n)
      k (p.nonneg k) hhalf.le)
    linarith


def CriticalEvenOffspring.BridgeDominated (p : CriticalEvenOffspring) (N : ℕ) (C : ℝ) : Prop :=
  ∀ (i : Fin N) (k : ℕ), (cond (p.iidLaw N) {d | totalStep d = -1}).real {d | d i = k} ≤
    C * p.mass k


theorem CriticalEvenOffspring.bridge_coordinate_domination (p : CriticalEvenOffspring) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop, p.BridgeDominated (2*n+1) K := by
  obtain ⟨C, hCpos, hC⟩ := p.iid_site_uniform_bound
  let B := Real.sqrt (2*Real.pi) / (p.sigma * Real.pi)
  have hB : 0 < B := div_pos (Real.sqrt_pos.mpr (by positivity))
    (mul_pos p.sigma_pos Real.pi_pos)
  have hden : Tendsto (fun n : ℕ => Real.sqrt (2*n+3) *
      (p.iidLaw (2*n+3)).real {d | totalStep d = -1}) atTop (𝓝 B) := by
    have hh := p.bridgePartition_limit.comp (tendsto_add_atTop_nat 1)
    convert hh using 1
    ext n
    dsimp only [Function.comp_apply]
    rw [p.bridgePartition_eq_iid]
    congr 2; push_cast; ring
  have hd := (tendsto_order.1 hden).1 (B/2) (by linarith)
  have hshift : ∀ᶠ n : ℕ in atTop, p.BridgeDominated (2*n+3) (4*C/B) := by
    filter_upwards [hd] with n hn
    intro i k
    have hm := p.nonneg k
    have hs : Real.sqrt (2*n+3) ≤ 2 * Real.sqrt (2*n+2) := by
      have h₁ := Real.sq_sqrt (show 0 ≤ (2*n+3 : ℝ) by positivity)
      have h₂ := Real.sq_sqrt (show 0 ≤ (2*n+2 : ℝ) by positivity)
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      nlinarith [Real.sqrt_nonneg (2*n+3), Real.sqrt_nonneg (2*n+2)]
    have hnum : Real.sqrt (2*n+3) *
        (p.iidLaw (2*n+3)).real {d | d i = k ∧ totalStep d = -1} ≤
        2*C*p.mass k := by
      rw [p.iid_coordinate_site (2*n+2)]
      have hc := hC (2*n+1) (-1-((k:ℤ)-1))
      norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, add_assoc] at hc
      have hs' := mul_le_mul_of_nonneg_right hs
        (mul_nonneg hm (show 0 ≤ (p.iidLaw (2*n+2)).real
          {d | totalStep d = -1-((k:ℤ)-1)} from measureReal_nonneg))
      have hc' := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2*p.mass k by positivity)
      nlinarith
    rw [p.iid_cond_real]
    simp only [Set.mem_ofPred_eq]
    calc
      _ = (Real.sqrt (2*n+3) *
          (p.iidLaw (2*n+3)).real {d | d i = k ∧ totalStep d = -1}) /
          (Real.sqrt (2*n+3) * (p.iidLaw (2*n+3)).real {d | totalStep d = -1}) := by
        rw [mul_div_mul_left _ _ (Real.sqrt_pos.mpr (by positivity)).ne']
      _ ≤ (2*C*p.mass k)/(B/2) := div_le_div₀ (by positivity) hnum (by positivity) hn.le
      _ = (4*C/B)*p.mass k := by ring
  refine ⟨4*C/B, by positivity, ?_⟩
  rw [← map_add_atTop_eq_nat 1]
  change ∀ᶠ n : ℕ in atTop, p.BridgeDominated (2*(n+1)+1) (4*C/B)
  simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.reduceAdd] using hshift


lemma integral_degreeFrequency_le {N : ℕ} (hN : 0 < N)
    (μ : Measure (Fin N → ℕ)) [IsFiniteMeasure μ] (k : ℕ) {a : ℝ}
    (ha : ∀ i, μ.real {d | d i = k} ≤ a) :
    (∫ d, degreeFrequency d k ∂μ) ≤ a := by
  simp only [degreeFrequency, integral_div, integral_finsetSum _
    (fun i _ => coordinate_indicator_integrable μ i k), integral_coordinate_indicator]
  apply (div_le_iff₀ (by positivity : (0:ℝ)<N)).2
  calc
    _ ≤ ∑ _ : Fin N, a := Finset.sum_le_sum (fun i _ => ha i)
    _ = a * N := by simp [mul_comm]


lemma integral_degreeFrequency_abs_le {N : ℕ} (hN : 0 < N)
    (μ : Measure (Fin N → ℕ)) [IsProbabilityMeasure μ] (k : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    (∫ d, |degreeFrequency d k-c| ∂μ) ≤ (∫ d, degreeFrequency d k ∂μ) + c := by
  have h := integral_mono (degreeFrequency_abs_integrable hN μ k c)
    ((degreeFrequency_integrable hN μ k).add (integrable_const c))
    (fun d => (abs_sub (degreeFrequency d k) c).trans_eq (by
      simp only [Pi.add_apply, abs_of_nonneg (degreeFrequency_nonneg d k), abs_of_nonneg hc]))
  change (∫ d, |degreeFrequency d k-c| ∂μ) ≤ ∫ d, degreeFrequency d k+c ∂μ at h
  simpa [integral_add (degreeFrequency_integrable hN μ k) (integrable_const c)] using h


theorem CriticalEvenOffspring.bridge_weighted_frequency_l1_limit (p : CriticalEvenOffspring) :
    Tendsto (fun n : ℕ => ∑' k : ℕ,
      (k:ℝ)^2 * ∫ d, |degreeFrequency d k-p.mass k| ∂p.bridgeLaw n) atTop (𝓝 0) := by
  obtain ⟨K, hK, hdom⟩ := p.bridge_coordinate_domination
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ k : ℕ,
      ‖(k:ℝ)^2 * ∫ d, |degreeFrequency d k-p.mass k| ∂p.bridgeLaw n‖ ≤
        (K+1)*((k:ℝ)^2*p.mass k) := by
    filter_upwards [hdom] with n hn k
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _)
      (integral_nonneg (fun _ => abs_nonneg _)))]
    have hi := integral_degreeFrequency_le (by omega) (p.bridgeLaw n) k (hn · k)
    have hj := integral_degreeFrequency_abs_le (by omega) (p.bridgeLaw n) k (p.nonneg k)
    nlinarith [mul_le_mul_of_nonneg_left (hj.trans (add_le_add_left hi _)) (sq_nonneg (k:ℝ))]
  have ht := tendsto_tsum_of_dominated_convergence (p.second.mul_left (K+1))
    (fun k : ℕ => by simpa using (p.bridge_frequency_l1_limit k).const_mul ((k:ℝ)^2)) hbound
  simpa using ht


lemma degreeFrequency_finite_support {N : ℕ} (d : Fin N → ℕ) :
    (Function.support (degreeFrequency d)).Finite := by
  apply (Set.finite_range d).subset
  intro k hk
  by_contra hn
  have hzero : degreeFrequency d k = 0 := by
    simp only [degreeFrequency]
    have heq : ∀ i : Fin N, d i ≠ k := fun i h => hn ⟨i,h⟩
    simp [heq]
  exact hk hzero


lemma summable_weighted_frequency_error (p : CriticalEvenOffspring) {N : ℕ}
    (d : Fin N → ℕ) : Summable (fun k : ℕ => (k:ℝ)^2*|degreeFrequency d k-p.mass k|) := by
  have hf : Summable (fun k : ℕ => (k:ℝ)^2*degreeFrequency d k) :=
    summable_of_hasFiniteSupport (Function.HasFiniteSupport.mul_right
      (fun k : ℕ => (k:ℝ)^2) (degreeFrequency_finite_support d))
  have hs := (hf.sub p.second).abs
  simpa only [← mul_sub, abs_mul, abs_sq] using hs


lemma moment_eq_tsum_frequency {N : ℕ} (d : Fin N → ℕ) :
    (∑ i : Fin N, (d i:ℝ)^2) / N = ∑' k : ℕ, (k:ℝ)^2*degreeFrequency d k := by
  have hi (i : Fin N) : Summable (fun k : ℕ => (k:ℝ)^2 * if d i=k then 1 else 0) := by
    apply summable_of_hasFiniteSupport
    apply (Set.finite_singleton (d i)).subset
    intro k hk
    by_contra h
    have hn : d i ≠ k := Ne.symm (by simpa only [Set.mem_singleton_iff] using h)
    simp [Function.mem_support, hn] at hk
  simp only [degreeFrequency, ← mul_div_assoc, Finset.mul_sum, tsum_div_const]
  rw [Summable.tsum_finsetSum (fun i _ => hi i)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_ite, eq_comm]


lemma CriticalEvenOffspring.bridge_integrable (p : CriticalEvenOffspring) (n : ℕ)
    (f : (Fin (2*n+1) → ℕ) → ℝ) : Integrable f (p.bridgeLaw n) := by
  have hs : {d : Fin (2*n+1) → ℕ | totalStep d = -1}.Finite := by
    rw [totalStep_bridge_range]
    exact Set.finite_range _
  have hi := IntegrableOn.of_finite (μ := p.bridgeLaw n) (f := f) hs
  have hae : ∀ᵐ d ∂p.bridgeLaw n, totalStep d = -1 := by
    exact ae_cond_mem (by measurability)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (s := {d | totalStep d = -1}) hae] at hi


lemma moment_deviation_le (p : CriticalEvenOffspring) {N : ℕ} (d : Fin N → ℕ) :
    |(∑ i : Fin N, (d i:ℝ)^2)/N - ∑' k : ℕ, (k:ℝ)^2*p.mass k| ≤
      ∑' k : ℕ, (k:ℝ)^2*|degreeFrequency d k-p.mass k| := by
  rw [moment_eq_tsum_frequency]
  have hf : Summable (fun k : ℕ => (k:ℝ)^2*degreeFrequency d k) :=
    summable_of_hasFiniteSupport (Function.HasFiniteSupport.mul_right
      (fun k : ℕ => (k:ℝ)^2) (degreeFrequency_finite_support d))
  rw [← hf.tsum_sub p.second]
  have h := norm_tsum_le_tsum_norm (hf.sub p.second).norm
  simpa only [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_sq] using h


def empiricalSecondMoment {N : ℕ} (d : Fin N → ℕ) : ℝ :=
  (∑ i : Fin N, (d i:ℝ)^2)/N


lemma empiricalSecondMoment_rotation {N : ℕ} [NeZero N] (m : Fin N) (d : Fin N → Fin N) :
    empiricalSecondMoment (fun i => (rotateDegrees m d i).val) =
      empiricalSecondMoment (fun i => (d i).val) := by
  unfold empiricalSecondMoment
  congr 1
  exact Equiv.sum_comp (Equiv.addRight m) (fun i => ((d i).val:ℝ)^2)


def CriticalEvenOffspring.secondMean (p : CriticalEvenOffspring) : ℝ :=
  ∑' k : ℕ, (k:ℝ)^2*p.mass k


lemma CriticalEvenOffspring.integral_moment_error_le (p : CriticalEvenOffspring)
    (n : ℕ) {K : ℝ} (hdom : p.BridgeDominated (2*n+1) K) :
    (∫ d, |empiricalSecondMoment d-p.secondMean| ∂p.bridgeLaw n) ≤
    ∑' k : ℕ, (k:ℝ)^2*∫ d, |degreeFrequency d k-p.mass k| ∂p.bridgeLaw n := by
  let F (k : ℕ) (d : Fin (2*n+1) → ℕ) := (k:ℝ)^2*|degreeFrequency d k-p.mass k|
  have hsum : Summable (fun k => ∫ d, ‖F k d‖ ∂p.bridgeLaw n) := by
    apply (p.second.mul_left (K+1)).of_nonneg_of_le (fun k => integral_nonneg (fun _ => norm_nonneg _))
    intro k
    have hi := integral_degreeFrequency_le (by omega) (p.bridgeLaw n) k (hdom · k)
    have hj := integral_degreeFrequency_abs_le (by omega) (p.bridgeLaw n) k (p.nonneg k)
    simp only [F, Real.norm_eq_abs, abs_mul, abs_sq, abs_abs, integral_const_mul]
    nlinarith [mul_le_mul_of_nonneg_left (hj.trans (add_le_add_left hi _)) (sq_nonneg (k:ℝ))]
  have heq := integral_tsum_of_summable_integral_norm (fun k => p.bridge_integrable n (F k)) hsum
  have hle := integral_mono (p.bridge_integrable n _) (p.bridge_integrable n _)
    (fun d => moment_deviation_le p d)
  change (∫ d, |empiricalSecondMoment d-p.secondMean| ∂p.bridgeLaw n) ≤
    ∫ d, ∑' k, F k d ∂p.bridgeLaw n at hle
  rw [← heq] at hle
  simpa only [F, integral_const_mul] using hle


theorem CriticalEvenOffspring.bridge_second_moment_l1_limit (p : CriticalEvenOffspring) :
    Tendsto (fun n : ℕ => ∫ d, |empiricalSecondMoment d-p.secondMean| ∂p.bridgeLaw n)
      atTop (𝓝 0) := by
  obtain ⟨K, _, hdom⟩ := p.bridge_coordinate_domination
  apply squeeze_zero' (Eventually.of_forall (fun _ => integral_nonneg (fun _ => abs_nonneg _)))
    _ p.bridge_weighted_frequency_l1_limit
  exact hdom.mono (fun n hn => p.integral_moment_error_le n hn)


lemma CriticalEvenOffspring.bridge_moment_deviation_bound (p : CriticalEvenOffspring)
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (p.bridgeLaw n).real {d | ε < |empiricalSecondMoment d-p.secondMean|} ≤
      (∫ d, |empiricalSecondMoment d-p.secondMean| ∂p.bridgeLaw n)/ε := by
  rw [le_div_iff₀ hε, mul_comm]
  apply le_trans _ (mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
    (p.bridge_integrable n _) ε)
  apply mul_le_mul_of_nonneg_left (measureReal_mono _) hε.le
  intro d hd
  exact (show ε < |empiricalSecondMoment d-p.secondMean| from hd).le


theorem CriticalEvenOffspring.bridge_second_moment_limit (p : CriticalEvenOffspring)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (p.bridgeLaw n).real
      {d | ε < |empiricalSecondMoment d-p.secondMean|}) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg) (fun n => p.bridge_moment_deviation_bound n hε)
  simpa using p.bridge_second_moment_l1_limit.div_const ε


lemma code_second_moment_probability_eq_bridge (p : CriticalEvenOffspring)
    (n : ℕ) (ε : ℝ) :
    codeEventProbability p (2*n+1)
      (fun d => ε < |empiricalSecondMoment (fun i => (d i).val)-p.secondMean|) =
    (p.bridgeLaw n).real {d | ε < |empiricalSecondMoment d-p.secondMean|} := by
  rw [codeEventProbability_eq_bridge p (by omega) _ (by
    intro m d
    rw [empiricalSecondMoment_rotation]), p.bridgePartition_eq_iid,
    p.bridgeEventMass_eq_iid (2*n+1) (fun d => ε < |empiricalSecondMoment d-p.secondMean|),
    p.bridgeLaw_real]
  congr 2
  ext d
  exact and_comm


theorem CriticalEvenOffspring.conditioned_second_moment (p : CriticalEvenOffspring)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => codeEventProbability p (2*n+1)
      (fun d => ε < |empiricalSecondMoment (fun i => (d i).val)-p.secondMean|))
      atTop (𝓝 0) := by
  simpa only [code_second_moment_probability_eq_bridge] using p.bridge_second_moment_limit hε

end FKCRT.TreeCoding

namespace FKCRT.TreeCoding


lemma iid_prefix_endpoint_bound (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (m r : ℕ) (j : ℤ) (E : Set (Fin m → ℕ)) {C : ℝ} (hC : 0 ≤ C)
    (hsite : ∀ k : ℤ, (Measure.pi (fun _ : Fin r => μ)).real {d | totalStep d = k} ≤ C) :
    (Measure.pi (fun _ : Fin (m+r) => μ)).real
      {d | (iidSplit m r d).1 ∈ E ∧ totalStep d = j} ≤
    C * (Measure.pi (fun _ : Fin m => μ)).real E := by
  let μ₁ := Measure.pi (fun _ : Fin m => μ)
  let μ₂ := Measure.pi (fun _ : Fin r => μ)
  have hset : {d : Fin (m+r) → ℕ | (iidSplit m r d).1 ∈ E ∧ totalStep d = j} =
      iidSplit m r ⁻¹' {x | x.1 ∈ E ∧ totalStep x.2 = j-totalStep x.1} := by
    ext d
    change (_ ∈ E ∧ totalStep d = j) ↔ (_ ∈ E ∧
      totalStep (iidSplit m r d).2 = j-totalStep (iidSplit m r d).1)
    rw [totalStep_split]
    constructor <;> rintro ⟨hE, h⟩ <;> exact ⟨hE, by omega⟩
  have hb : (μ₁.prod μ₂) {x | x.1 ∈ E ∧ totalStep x.2 = j-totalStep x.1} ≤
      ENNReal.ofReal C * μ₁ E := by
    rw [Measure.prod_apply (by measurability)]
    have hsect (d : Fin m → ℕ) : μ₂ (Prod.mk d ⁻¹'
        {x | x.1 ∈ E ∧ totalStep x.2 = j-totalStep x.1}) ≤
        E.indicator (fun _ => ENNReal.ofReal C) d := by
      by_cases hd : d ∈ E
      · rw [Set.indicator_of_mem hd]
        have hs : Prod.mk d ⁻¹' {x : (Fin m → ℕ) × (Fin r → ℕ) | x.1 ∈ E ∧ totalStep x.2 = j-totalStep x.1} =
            {u | totalStep u = j-totalStep d} := by ext u; simp [hd]
        rw [hs, ← ENNReal.ofReal_toReal (measure_ne_top μ₂ _)]
        exact ENNReal.ofReal_le_ofReal (hsite _)
      · have hs : Prod.mk d ⁻¹' {x : (Fin m → ℕ) × (Fin r → ℕ) | x.1 ∈ E ∧ totalStep x.2 = j-totalStep x.1} = ∅ := by
          ext u; simp [hd]
        simp [hs, hd]
    apply (lintegral_mono hsect).trans_eq
    rw [lintegral_indicator (by measurability), lintegral_const, Measure.restrict_apply_univ]
  rw [measureReal_def, hset, (iidSplit_preserving μ m r).measure_preimage (by measurability)]
  apply (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ₁ E)) hb).trans_eq
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC]
  rfl


def CriticalEvenOffspring.PrefixDominated (p : CriticalEvenOffspring)
    (N : ℕ) (K : ℝ) : Prop :=
  ∀ m r : ℕ, m+r=N → N ≤ 2*r → ∀ E : Set (Fin m → ℕ),
    (cond (p.iidLaw (m+r)) {d | totalStep d = -1}).real
      {d | (iidSplit m r d).1 ∈ E} ≤ K * (p.iidLaw m).real E


theorem CriticalEvenOffspring.bridge_prefix_domination (p : CriticalEvenOffspring) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop, p.PrefixDominated (2*n+1) K := by
  obtain ⟨C, hCpos, hC⟩ := p.iid_site_uniform_bound
  let B := Real.sqrt (2*Real.pi) / (p.sigma * Real.pi)
  have hB : 0 < B := div_pos (Real.sqrt_pos.mpr (by positivity))
    (mul_pos p.sigma_pos Real.pi_pos)
  have hden : Tendsto (fun n : ℕ => Real.sqrt ((2*n+1 : ℕ) : ℝ) *
      (p.iidLaw (2*n+1)).real {d | totalStep d = -1}) atTop (𝓝 B) := by
    convert p.bridgePartition_limit using 1
    ext n
    rw [p.bridgePartition_eq_iid]
    push_cast
    rfl
  refine ⟨4*C/B, by positivity, ?_⟩
  filter_upwards [(tendsto_order.1 hden).1 (B/2) (by linarith)] with n hn
  intro m r hsum hhalf E
  have hr : 0 < r := by omega
  have hsr : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hr)
  have hsN : 0 < Real.sqrt ((m+r : ℕ) : ℝ) := Real.sqrt_pos.mpr (by norm_cast; omega)
  have hratio : Real.sqrt ((m+r : ℕ) : ℝ) ≤ 2 * Real.sqrt (r : ℝ) := by
    have hh : (m+r : ℝ) ≤ 2*r := by exact_mod_cast (show m+r ≤ 2*r by omega)
    have h₁ := Real.sq_sqrt (show (0:ℝ) ≤ ((m+r : ℕ) : ℝ) by positivity)
    have h₂ := Real.sq_sqrt (show (0:ℝ) ≤ r by positivity)
    push_cast at h₁ ⊢
    nlinarith [Real.sqrt_nonneg (m+r)]
  have hsite (j : ℤ) : (p.iidLaw r).real {d | totalStep d = j} ≤ C / Real.sqrt (r : ℝ) := by
    obtain ⟨r', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
    have hc := hC r' j
    rw [le_div_iff₀ hsr]
    simpa [Nat.cast_add, Nat.cast_one, mul_comm] using hc
  have hpre := iid_prefix_endpoint_bound p.law.toMeasure m r (-1) E
    (show 0 ≤ C / Real.sqrt (r:ℝ) by positivity) hsite
  have hnum : Real.sqrt ((m+r : ℕ) : ℝ) *
      (p.iidLaw (m+r)).real {d | (iidSplit m r d).1 ∈ E ∧ totalStep d = -1} ≤
      2*C*(p.iidLaw m).real E := by
    have hA : Real.sqrt ((m+r : ℕ) : ℝ) * (C / Real.sqrt (r:ℝ)) ≤ 2*C := by
      rw [← mul_div_assoc, div_le_iff₀ hsr]
      nlinarith
    calc
      _ ≤ Real.sqrt ((m+r : ℕ) : ℝ) * (C / Real.sqrt (r:ℝ) * (p.iidLaw m).real E) :=
        mul_le_mul_of_nonneg_left hpre hsN.le
      _ = (Real.sqrt ((m+r : ℕ) : ℝ) * (C / Real.sqrt (r:ℝ))) * (p.iidLaw m).real E := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hA measureReal_nonneg
  have hd : B/2 < Real.sqrt ((m+r : ℕ) : ℝ) *
      (p.iidLaw (m+r)).real {d | totalStep d = -1} := by
    change B/2 < Real.sqrt ((m+r : ℕ) : ℝ) * p.iidSiteProbability (m+r) (-1)
    change B/2 < Real.sqrt ((2*n+1 : ℕ) : ℝ) * p.iidSiteProbability (2*n+1) (-1) at hn
    simpa only [hsum] using hn
  rw [p.iid_cond_real]
  simp only [Set.mem_ofPred_eq]
  calc
    _ = (Real.sqrt ((m+r : ℕ) : ℝ) *
        (p.iidLaw (m+r)).real {d | (iidSplit m r d).1 ∈ E ∧ totalStep d = -1}) /
      (Real.sqrt ((m+r : ℕ) : ℝ) * (p.iidLaw (m+r)).real {d | totalStep d = -1}) := by
      rw [mul_div_mul_left _ _ hsN.ne']
    _ ≤ (2*C*(p.iidLaw m).real E)/(B/2) :=
      div_le_div₀ (by positivity) hnum (by positivity) hd.le
    _ = (4*C/B)*(p.iidLaw m).real E := by ring


def CriticalEvenOffspring.PrefixDominatedFraction (p : CriticalEvenOffspring)
    (N J : ℕ) (K : ℝ) : Prop :=
  ∀ m r : ℕ, m+r=N → N ≤ J*r → ∀ E : Set (Fin m → ℕ),
    (cond (p.iidLaw (m+r)) {d | totalStep d = -1}).real
      {d | (iidSplit m r d).1 ∈ E} ≤ K * (p.iidLaw m).real E


theorem CriticalEvenOffspring.bridge_prefix_domination_fraction (p : CriticalEvenOffspring)
    (J : ℕ) (hJ : 0<J) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop, p.PrefixDominatedFraction (2*n+1) J K := by
  obtain ⟨C, hCpos, hC⟩ := p.iid_site_uniform_bound
  let B := Real.sqrt (2*Real.pi) / (p.sigma * Real.pi)
  have hB : 0 < B := div_pos (Real.sqrt_pos.mpr (by positivity))
    (mul_pos p.sigma_pos Real.pi_pos)
  have hden : Tendsto (fun n : ℕ => Real.sqrt ((2*n+1 : ℕ) : ℝ) *
      (p.iidLaw (2*n+1)).real {d | totalStep d = -1}) atTop (𝓝 B) := by
    convert p.bridgePartition_limit using 1
    ext n
    rw [p.bridgePartition_eq_iid]
    push_cast
    rfl
  refine ⟨2*J*C/B, by positivity, ?_⟩
  filter_upwards [(tendsto_order.1 hden).1 (B/2) (by linarith)] with n hn
  intro m r hsum hhalf E
  have hr : 0 < r := by
    by_contra hn
    have hrz : r=0 := by omega
    simp only [hrz,mul_zero] at hhalf
    omega
  have hsr : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hr)
  have hsN : 0 < Real.sqrt ((m+r : ℕ) : ℝ) := Real.sqrt_pos.mpr (by norm_cast; omega)
  have hratio : Real.sqrt ((m+r : ℕ) : ℝ) ≤ (J:ℝ) * Real.sqrt (r : ℝ) := by
    have hh : (m+r : ℝ) ≤ J*r := by exact_mod_cast (show m+r ≤ J*r by omega)
    have hJ1 : (1:ℝ) ≤ J := by exact_mod_cast hJ
    have hjr : (J:ℝ)*r ≤ J^2*r := by
      have hr0 : (0:ℝ) ≤ r := by positivity
      nlinarith
    have hpos : 0 ≤ (J:ℝ)*Real.sqrt (r:ℝ) := by positivity
    have h₁ := Real.sq_sqrt (show (0:ℝ) ≤ ((m+r : ℕ) : ℝ) by positivity)
    have h₂ := Real.sq_sqrt (show (0:ℝ) ≤ r by positivity)
    have h₂x := congrArg (fun t : ℝ => (J:ℝ)^2*t) h₂
    push_cast at h₁ ⊢
    nlinarith [Real.sqrt_nonneg (m+r)]
  have hsite (j : ℤ) : (p.iidLaw r).real {d | totalStep d = j} ≤ C / Real.sqrt (r : ℝ) := by
    obtain ⟨r', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
    have hc := hC r' j
    rw [le_div_iff₀ hsr]
    simpa [Nat.cast_add, Nat.cast_one, mul_comm] using hc
  have hpre := iid_prefix_endpoint_bound p.law.toMeasure m r (-1) E
    (show 0 ≤ C / Real.sqrt (r:ℝ) by positivity) hsite
  have hnum : Real.sqrt ((m+r : ℕ) : ℝ) *
      (p.iidLaw (m+r)).real {d | (iidSplit m r d).1 ∈ E ∧ totalStep d = -1} ≤
      J*C*(p.iidLaw m).real E := by
    have hA : Real.sqrt ((m+r : ℕ) : ℝ) * (C / Real.sqrt (r:ℝ)) ≤ J*C := by
      rw [← mul_div_assoc, div_le_iff₀ hsr]
      nlinarith
    calc
      _ ≤ Real.sqrt ((m+r : ℕ) : ℝ) * (C / Real.sqrt (r:ℝ) * (p.iidLaw m).real E) :=
        mul_le_mul_of_nonneg_left hpre hsN.le
      _ = (Real.sqrt ((m+r : ℕ) : ℝ) * (C / Real.sqrt (r:ℝ))) * (p.iidLaw m).real E := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hA measureReal_nonneg
  have hd : B/2 < Real.sqrt ((m+r : ℕ) : ℝ) *
      (p.iidLaw (m+r)).real {d | totalStep d = -1} := by
    change B/2 < Real.sqrt ((m+r : ℕ) : ℝ) * p.iidSiteProbability (m+r) (-1)
    change B/2 < Real.sqrt ((2*n+1 : ℕ) : ℝ) * p.iidSiteProbability (2*n+1) (-1) at hn
    simpa only [hsum] using hn
  rw [p.iid_cond_real]
  simp only [Set.mem_ofPred_eq]
  calc
    _ = (Real.sqrt ((m+r : ℕ) : ℝ) *
        (p.iidLaw (m+r)).real {d | (iidSplit m r d).1 ∈ E ∧ totalStep d = -1}) /
      (Real.sqrt ((m+r : ℕ) : ℝ) * (p.iidLaw (m+r)).real {d | totalStep d = -1}) := by
      rw [mul_div_mul_left _ _ hsN.ne']
    _ ≤ (J*C*(p.iidLaw m).real E)/(B/2) :=
      div_le_div₀ (by positivity) hnum (by positivity) hd.le
    _ = (2*J*C/B)*(p.iidLaw m).real E := by ring


end FKCRT.TreeCoding
end

end OAI
