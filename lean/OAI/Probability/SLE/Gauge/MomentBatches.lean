import OAI.Probability.SLE.MomentGauge

namespace OAI

/-! The dyadic moment batches in Lemma `gauge:multiplicity` of the first paper. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SLEExactGauge.MomentBatches

def dyadic (k : ℤ) : ℝ := (2 : ℝ) ^ k

def weight (n : ℕ) (m : ℝ) (k : ℤ) : ℝ := (4 : ℝ) ^ n * dyadic k ^ n / m

def copies (n : ℕ) (m T : ℝ) (k : ℤ) : ℕ :=
  if dyadic k ≤ T then ⌊weight n m k⌋₊ else 0

lemma dyadic_pos (k : ℤ) : 0 < dyadic k := zpow_pos (by norm_num) k

lemma dyadic_step (k : ℤ) : dyadic (k - 1) = dyadic k / 2 := by
  simp [dyadic, zpow_sub₀]

lemma denominator_pos {n : ℕ} (hn : 1 ≤ n) : 0 < 1 - (1 / 2 : ℝ) ^ n := by
  exact sub_pos.mpr (pow_lt_one₀ (by norm_num) (by norm_num) (by omega))

/-- A finite selection of dyadic levels below `x` is bounded by the complete
geometric tail. Missing levels only improve the bound. -/
lemma dyadic_sum_le {n : ℕ} (hn : 1 ≤ n) (S : Finset ℤ)
    {x : ℝ} (hx : 0 ≤ x) (hS : ∀ k ∈ S, dyadic k ≤ x) :
    ∑ k ∈ S, dyadic k ^ n ≤ x ^ n / (1 - (1 / 2 : ℝ) ^ n) := by
  classical
  induction S using Finset.induction_on_max generalizing x with
  | empty =>
      rw [Finset.sum_empty]
      exact div_nonneg (pow_nonneg hx _) (denominator_pos hn).le
  | insert a S hmax ih =>
      have ha : a ∉ S := fun ha => (hmax a ha).false
      have hprev : ∀ k ∈ S, dyadic k ≤ dyadic (a - 1) := by
        intro k hk
        exact zpow_le_zpow_right₀ (by norm_num) (show k ≤ a - 1 by have := hmax k hk; omega)
      have hi := ih (dyadic_pos (a - 1)).le hprev
      have hax := hS a (Finset.mem_insert_self _ _)
      rw [Finset.sum_insert ha]
      calc
        _ ≤ dyadic a ^ n + dyadic (a - 1) ^ n / (1 - (1 / 2 : ℝ) ^ n) :=
          add_le_add le_rfl hi
        _ = dyadic a ^ n / (1 - (1 / 2 : ℝ) ^ n) := by
          have hp : dyadic (a - 1) ^ n = dyadic a ^ n * (1 / 2 : ℝ) ^ n := by
            rw [dyadic_step, div_pow, one_div_pow]
            ring
          apply (eq_div_iff (denominator_pos hn).ne').mpr
          rw [add_mul, div_mul_cancel₀ _ (denominator_pos hn).ne', hp]
          ring
        _ ≤ x ^ n / (1 - (1 / 2 : ℝ) ^ n) :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ (dyadic_pos a).le hax n)
            (denominator_pos hn).le

lemma weight_nonneg {n : ℕ} {m : ℝ} (hm : 0 < m) (k : ℤ) : 0 ≤ weight n m k := by
  unfold weight
  exact div_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (dyadic_pos k).le _)) hm.le

lemma copies_le_weight {n : ℕ} {m T : ℝ} (hm : 0 < m) (k : ℤ) :
    (copies n m T k : ℝ) ≤ weight n m k := by
  unfold copies
  split_ifs
  · exact Nat.floor_le (weight_nonneg hm k)
  · simpa only [Nat.cast_zero] using weight_nonneg (n := n) hm k

lemma hit_count_upper {n : ℕ} (hn : 1 ≤ n) {m T x : ℝ}
    (hm : 0 < m) (hx : 0 ≤ x) (S : Finset ℤ) :
    ∑ k ∈ S, (if 16 * dyadic k ≤ x then (copies n m T k : ℝ) else 0) ≤
      ((4 : ℝ) ^ n / (m * 16 ^ n * (1 - (1 / 2 : ℝ) ^ n))) * x ^ n := by
  classical
  rw [← Finset.sum_filter]
  let A := S.filter (fun k => 16 * dyadic k ≤ x)
  have hA : ∀ k ∈ A, dyadic k ≤ x / 16 := by
    intro k hk
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).mpr
      (by simpa [mul_comm] using (Finset.mem_filter.mp hk).2)
  calc
    _ ≤ ∑ k ∈ A, weight n m k := Finset.sum_le_sum (fun k _ => copies_le_weight hm k)
    _ = ((4 : ℝ) ^ n / m) * ∑ k ∈ A, dyadic k ^ n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      dsimp [weight]
      ring
    _ ≤ ((4 : ℝ) ^ n / m) * ((x / 16) ^ n / (1 - (1 / 2 : ℝ) ^ n)) :=
      mul_le_mul_of_nonneg_left (dyadic_sum_le hn A (by positivity) hA) (by positivity)
    _ = _ := by rw [div_pow]; field_simp

lemma integral_hit_count {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    (n : ℕ) (m T c : ℝ) (S : Finset ℤ) :
    (∫ ω, ∑ k ∈ S, if c * dyadic k ≤ X ω then (copies n m T k : ℝ) else 0 ∂P) =
      ∑ k ∈ S, (copies n m T k : ℝ) * P.real {ω | c * dyadic k ≤ X ω} := by
  classical
  have he (k : ℤ) : MeasurableSet {ω | c * dyadic k ≤ X ω} :=
    measurableSet_le measurable_const hX
  have hi (k : ℤ) : Integrable
      (fun ω => if c * dyadic k ≤ X ω then (copies n m T k : ℝ) else 0) P := by
    exact (integrable_const _).indicator (he k)
  rw [integral_finsetSum S (fun k _ => hi k)]
  apply Finset.sum_congr rfl
  intro k hk
  simpa only [Set.indicator, Set.mem_ofPred_eq, smul_eq_mul, mul_comm] using
    integral_indicator_const (μ := P) (copies n m T k : ℝ) (he k)

/-- The upper batch probability estimate with its precise geometric constant.
Only the positive finite `n`th moment of the nonnegative random mass is used. -/
theorem upper_batch_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    (hX0 : ∀ ω, 0 ≤ X ω) {n : ℕ} (hn : 1 ≤ n)
    {m T : ℝ} (hm : 0 < m) (hInt : Integrable (fun ω => X ω ^ n) P)
    (hMoment : ∫ ω, X ω ^ n ∂P = m) :
    ∑' k : ℤ, (copies n m T k : ℝ) * P.real {ω | 16 * dyadic k ≤ X ω} ≤
      (4 : ℝ) ^ n / 16 ^ n / (1 - (1 / 2 : ℝ) ^ n) := by
  classical
  apply Real.tsum_le_of_sum_le (fun k => mul_nonneg (Nat.cast_nonneg _) (measureReal_nonneg))
  intro S
  let C := (4 : ℝ) ^ n / (m * 16 ^ n * (1 - (1 / 2 : ℝ) ^ n))
  have hi (k : ℤ) : Integrable
      (fun ω => if 16 * dyadic k ≤ X ω then (copies n m T k : ℝ) else 0) P :=
    (integrable_const _).indicator (measurableSet_le measurable_const hX)
  calc
    _ = ∫ ω, ∑ k ∈ S, if 16 * dyadic k ≤ X ω then (copies n m T k : ℝ) else 0 ∂P :=
      (integral_hit_count P X hX n m T 16 S).symm
    _ ≤ ∫ ω, C * X ω ^ n ∂P := integral_mono
      (integrable_finsetSum S (fun k _ => hi k)) (hInt.const_mul C)
      (fun ω => hit_count_upper hn hm (hX0 ω) S)
    _ = C * m := by rw [integral_const_mul, hMoment]
    _ = _ := by dsimp [C]; field_simp

lemma floor_half_sub_half {w : ℝ} (_hw : 0 ≤ w) : w / 2 - 1 / 2 ≤ (⌊w⌋₊ : ℝ) := by
  by_cases h1 : 1 ≤ w
  · exact (by linarith : w / 2 - 1 / 2 ≤ w / 2).trans (Nat.div_two_lt_floor h1).le
  · exact (by linarith : w / 2 - 1 / 2 ≤ 0).trans (Nat.cast_nonneg _)

lemma dyadic_level {x : ℝ} (hx : 0 < x) :
    ∃ k : ℤ, x / 2 < dyadic k ∧ dyadic k ≤ x := by
  obtain ⟨k, hlo, hhi⟩ := exists_mem_Ico_zpow hx (by norm_num : (1 : ℝ) < 2)
  refine ⟨k, ?_, hlo⟩
  have hs : (2 : ℝ) ^ (k + 1) = 2 * dyadic k := by
    simp [dyadic, zpow_add₀, mul_comm]
  rw [hs] at hhi
  linarith

/-- One well-chosen dyadic level already gives the required lower count.
This avoids charging a floor error at every dyadic level. -/
lemma hit_count_lower {n : ℕ} (hn : 1 ≤ n) {m T x : ℝ} (hm : 0 < m)
    (hx : 0 ≤ x) (hxT : x ≤ T) (S : Finset ℤ)
    (hS : ∀ k, copies n m T k ≠ 0 → k ∈ S) :
    (2 : ℝ) ^ n / (2 * m) * x ^ n - 1 / 2 ≤
      ∑ k ∈ S, if dyadic k ≤ x then (copies n m T k : ℝ) else 0 := by
  classical
  have hnonneg : 0 ≤ ∑ k ∈ S,
      if dyadic k ≤ x then (copies n m T k : ℝ) else 0 :=
    Finset.sum_nonneg (fun k _ => by split_ifs <;> positivity)
  obtain rfl | hxp := hx.eq_or_lt
  · simpa only [zero_pow (by omega : n ≠ 0), mul_zero, zero_sub] using
      (show -(1 / 2 : ℝ) ≤ _ from (by norm_num : -(1 / 2 : ℝ) ≤ 0).trans hnonneg)
  obtain ⟨k, hklo, hkhi⟩ := dyadic_level hxp
  have hkT : dyadic k ≤ T := hkhi.trans hxT
  have hw : (2 : ℝ) ^ n * x ^ n / m ≤ weight n m k := by
    have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ x / 2) hklo.le n
    have hp' := mul_le_mul_of_nonneg_left hp (show 0 ≤ (4 : ℝ) ^ n / m by positivity)
    unfold weight
    calc
      _ = ((4 : ℝ) ^ n / m) * (x / 2) ^ n := by
        rw [div_pow, show (4 : ℝ) ^ n = 2 ^ n * 2 ^ n by rw [← mul_pow]; norm_num]
        field_simp
      _ ≤ ((4 : ℝ) ^ n / m) * dyadic k ^ n := hp'
      _ = _ := by ring
  have hfloor : weight n m k / 2 - 1 / 2 ≤ (copies n m T k : ℝ) := by
    simpa only [copies, ite_eq_left hkT] using floor_half_sub_half (weight_nonneg hm k)
  have hsingle : (copies n m T k : ℝ) ≤
      ∑ j ∈ S, if dyadic j ≤ x then (copies n m T j : ℝ) else 0 := by
    by_cases hz : copies n m T k = 0
    · simpa only [hz, Nat.cast_zero] using hnonneg
    · have hs := Finset.single_le_sum
        (fun j (_ : j ∈ S) => show 0 ≤ (if dyadic j ≤ x then (copies n m T j : ℝ) else 0)
          from by split_ifs <;> positivity) (hS k hz)
      simpa only [ite_eq_left hkhi] using hs
  have hcoeff : (2 : ℝ) ^ n / (2 * m) * x ^ n = ((2 : ℝ) ^ n * x ^ n / m) / 2 := by
    ring
  rw [hcoeff]
  linarith

/-- The `(n+1)`st moment bounds the loss above the paper's cutoff
`T = 4 M / m`; a retained `3m/4` moment leaves at least `m/2`. -/
theorem retained_truncated_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → ℝ) (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω)
    (n : ℕ) {m M : ℝ} (hm : 0 < m) (hM : 0 < M)
    (hi : Integrable (fun ω => Y ω ^ n) P)
    (hi' : Integrable (fun ω => Y ω ^ (n + 1)) P)
    (hretained : 3 * m / 4 ≤ ∫ ω, Y ω ^ n ∂P)
    (hnext : (∫ ω, Y ω ^ (n + 1) ∂P) ≤ M) :
    m / 2 ≤ ∫ ω in {ω | Y ω ≤ 4 * M / m}, Y ω ^ n ∂P := by
  let T := 4 * M / m
  have hT : 0 < T := by dsimp [T]; positivity
  have hset : MeasurableSet {ω | Y ω ≤ T} := measurableSet_le hY measurable_const
  have htail : (∫ ω in {ω | Y ω ≤ T}ᶜ, Y ω ^ n ∂P) ≤ M / T := by
    calc
      _ = ∫ ω, {ω | Y ω ≤ T}ᶜ.indicator (fun ω => Y ω ^ n) ω ∂P :=
        (integral_indicator hset.compl).symm
      _ ≤ ∫ ω, Y ω ^ (n + 1) / T ∂P := by
        apply integral_mono (hi.indicator hset.compl) (hi'.div_const T)
        intro ω
        by_cases hω : Y ω ≤ T
        · simp only [Set.indicator, Set.mem_compl_iff, Set.mem_ofPred_eq, hω, not_true_eq_false,
            ↓reduceIte]
          exact div_nonneg (pow_nonneg (hY0 ω) _) hT.le
        · simp only [Set.indicator, Set.mem_compl_iff, Set.mem_ofPred_eq, hω, not_false_eq_true,
            ↓reduceIte]
          apply (le_div_iff₀ hT).mpr
          calc
            Y ω ^ n * T ≤ Y ω ^ n * Y ω :=
              mul_le_mul_of_nonneg_left (le_of_not_ge hω) (pow_nonneg (hY0 ω) _)
            _ = Y ω ^ (n + 1) := (pow_succ _ _).symm
      _ ≤ M / T := by rw [integral_div]; exact div_le_div_of_nonneg_right hnext hT.le
  have hdecomp := integral_add_compl hset hi
  have hMT : M / T = m / 4 := by dsimp [T]; field_simp
  rw [hMT] at htail
  change m / 2 ≤ ∫ ω in {ω | Y ω ≤ T}, Y ω ^ n ∂P
  linarith

/-- The lower batch probability estimate. The `1/2` loss is slightly stronger
than the paper's `1 / (2 * (1 - 2⁻ⁿ))` loss. -/
theorem lower_batch_probability_finset {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : Measurable Y)
    (hY0 : ∀ ω, 0 ≤ Y ω) {n : ℕ} (hn : 1 ≤ n) {m T : ℝ} (hm : 0 < m)
    (hi : Integrable (fun ω => Y ω ^ n) P)
    (htrunc : m / 2 ≤ ∫ ω in {ω | Y ω ≤ T}, Y ω ^ n ∂P)
    (S : Finset ℤ) (hS : ∀ k, copies n m T k ≠ 0 → k ∈ S) :
    (2 : ℝ) ^ n / 4 - 1 / 2 ≤
      ∑ k ∈ S, (copies n m T k : ℝ) * P.real {ω | dyadic k ≤ Y ω} := by
  classical
  let C := (2 : ℝ) ^ n / (2 * m)
  let F := {ω | Y ω ≤ T}.indicator (fun ω => Y ω ^ n)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hset : MeasurableSet {ω | Y ω ≤ T} := measurableSet_le hY measurable_const
  have hFi : Integrable F P := hi.indicator hset
  have hcount (k : ℤ) : Integrable
      (fun ω => if dyadic k ≤ Y ω then (copies n m T k : ℝ) else 0) P :=
    (integrable_const _).indicator (measurableSet_le measurable_const hY)
  have hbound (ω : Ω) : C * F ω - 1 / 2 ≤
      ∑ k ∈ S, if dyadic k ≤ Y ω then (copies n m T k : ℝ) else 0 := by
    by_cases hω : Y ω ≤ T
    · simpa only [F, Set.indicator, Set.mem_ofPred_eq, ite_eq_left hω, C] using
        hit_count_lower hn hm (hY0 ω) hω S hS
    · simp only [F, Set.indicator, Set.mem_ofPred_eq, ite_eq_right hω, mul_zero, zero_sub]
      exact (by norm_num : -(1 / 2 : ℝ) ≤ 0).trans
        (Finset.sum_nonneg (fun k _ => by split_ifs <;> positivity))
  have hint := integral_mono ((hFi.const_mul C).sub (integrable_const (1 / 2 : ℝ)))
    (integrable_finsetSum S (fun k _ => hcount k)) hbound
  change (∫ ω, C * F ω - 1 / 2 ∂P) ≤
    ∫ ω, ∑ k ∈ S, if dyadic k ≤ Y ω then (copies n m T k : ℝ) else 0 ∂P at hint
  rw [integral_sub (hFi.const_mul C) (integrable_const (1 / 2 : ℝ)), integral_const_mul,
    integral_const] at hint
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hint
  have hF : ∫ ω, F ω ∂P = ∫ ω in {ω | Y ω ≤ T}, Y ω ^ n ∂P := integral_indicator hset
  rw [hF] at hint
  have hl := mul_le_mul_of_nonneg_left htrunc hC
  have he : C * (m / 2) = (2 : ℝ) ^ n / 4 := by dsimp [C]; field_simp; ring
  rw [he] at hl
  have hprob := integral_hit_count P Y hY n m T 1 S
  simp only [one_mul] at hprob
  rw [hprob] at hint
  linarith

lemma lower_constant {n : ℕ} (hn : 3 ≤ n) :
    (2 : ℝ) ^ n / 8 ≤ (2 : ℝ) ^ n / 4 - 1 / 2 := by
  have hp : (4 : ℝ) ≤ 2 ^ n := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 2 ≤ n by omega)
    norm_num at h ⊢
    exact h
  linarith

lemma copies_positive_bounds {n : ℕ} (hn : 1 ≤ n) {m T : ℝ} (hm : 0 < m)
    {k : ℤ} (hk : copies n m T k ≠ 0) :
    min 1 (m / (4 : ℝ) ^ n) ≤ dyadic k ∧ dyadic k ≤ T := by
  have hcut : dyadic k ≤ T := by
    by_contra hc
    simp only [copies, ite_eq_right hc] at hk
    exact hk rfl
  have hfloor : 0 < ⌊weight n m k⌋₊ := by
    simpa only [copies, ite_eq_left hcut, Nat.pos_iff_ne_zero] using hk
  have hw : 1 ≤ weight n m k := Nat.floor_pos.mp hfloor
  have hnum : m / (4 : ℝ) ^ n ≤ dyadic k ^ n := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 ^ n)).mpr
    have hm' := (le_div_iff₀ hm).mp hw
    simpa only [weight, one_mul, mul_one, mul_comm] using hm'
  refine ⟨?_, hcut⟩
  rcases le_total 1 (dyadic k) with hlarge | hsmall
  · exact (min_le_left _ _).trans hlarge
  · have hp : dyadic k ^ n ≤ dyadic k := by
      simpa only [Real.rpow_natCast] using Real.rpow_le_self_of_le_one
        (dyadic_pos k).le hsmall (show (1 : ℝ) ≤ n by exact_mod_cast hn)
    exact (min_le_right _ _).trans (hnum.trans hp)

lemma copies_support_finite {n : ℕ} (hn : 1 ≤ n) {m T : ℝ} (hm : 0 < m) :
    Set.Finite {k : ℤ | copies n m T k ≠ 0} := by
  let b := min 1 (m / (4 : ℝ) ^ n)
  have hb : 0 < b := lt_min zero_lt_one (by positivity)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (Set.finite_Icc (⌈Real.log b / Real.log 2⌉ : ℤ)
    (⌊Real.log T / Real.log 2⌋ : ℤ)).subset
  intro k hk
  obtain ⟨hlo, hhi⟩ := copies_positive_bounds hn hm hk
  constructor
  · apply Int.ceil_le.mpr
    apply (div_le_iff₀ hlog).mpr
    exact (Real.le_zpow_iff_log_le hb (by norm_num : (0 : ℝ) < 2)).mp hlo
  · apply Int.le_floor.mpr
    apply (le_div_iff₀ hlog).mpr
    exact Real.le_log_of_zpow_le (by norm_num : (0 : ℝ) < 2) hhi

/-- The lower batch inequality for the whole integer sum, with no auxiliary
finite support assumption. -/
theorem lower_batch_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : Measurable Y)
    (hY0 : ∀ ω, 0 ≤ Y ω) {n : ℕ} (hn : 3 ≤ n) {m M : ℝ}
    (hm : 0 < m) (hM : 0 < M)
    (hi : Integrable (fun ω => Y ω ^ n) P)
    (hi' : Integrable (fun ω => Y ω ^ (n + 1)) P)
    (hretained : 3 * m / 4 ≤ ∫ ω, Y ω ^ n ∂P)
    (hnext : (∫ ω, Y ω ^ (n + 1) ∂P) ≤ M) :
    (2 : ℝ) ^ n / 8 ≤ ∑' k : ℤ,
      (copies n m (4 * M / m) k : ℝ) * P.real {ω | dyadic k ≤ Y ω} := by
  classical
  have hn1 : 1 ≤ n := by omega
  let S := (copies_support_finite hn1 (T := 4 * M / m) hm).toFinset
  have hs : ∀ k, copies n m (4 * M / m) k ≠ 0 → k ∈ S := by
    intro k hk
    exact (copies_support_finite hn1 (T := 4 * M / m) hm).mem_toFinset.mpr hk
  rw [tsum_eq_sum (s := S) (fun k hk => by
    have hz : copies n m (4 * M / m) k = 0 := by
      by_contra hc
      exact hk (hs k hc)
    simp only [hz, Nat.cast_zero, zero_mul])]
  apply (lower_constant hn).trans
  exact lower_batch_probability_finset P Y hY hY0 hn1 hm hi
    (retained_truncated_moment P Y hY hY0 n hm hM hi hi' hretained hnext) S hs

lemma copies_eq_target (κ : ℝ) (W : SLEExactGauge.Target.WienerLaw) (n : ℕ) (k : ℤ) :
    copies n (SLEExactGauge.Target.moment κ W n)
      (SLEExactGauge.Target.threshold κ W n) k = SLEExactGauge.Target.multiplicity κ W n k := rfl

/-- The upper inequality in the exact notation of the moment-gauge construction. -/
theorem target_upper_batch_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    (hX0 : ∀ ω, 0 ≤ X ω) (κ : ℝ) (W : SLEExactGauge.Target.WienerLaw)
    {n : ℕ} (hn : 1 ≤ n) (hm : 0 < SLEExactGauge.Target.moment κ W n)
    (hi : Integrable (fun ω => X ω ^ n) P)
    (he : ∫ ω, X ω ^ n ∂P = SLEExactGauge.Target.moment κ W n) :
    ∑' k : ℤ, (SLEExactGauge.Target.multiplicity κ W n k : ℝ) *
      P.real {ω | 16 * (2 : ℝ) ^ k ≤ X ω} ≤
        (4 : ℝ) ^ n / 16 ^ n / (1 - (1 / 2 : ℝ) ^ n) :=
  upper_batch_probability P X hX hX0 hn hm hi he

/-- The success inequality in the exact notation of the moment-gauge construction. -/
theorem target_lower_batch_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : Measurable Y)
    (hY0 : ∀ ω, 0 ≤ Y ω) (κ : ℝ) (W : SLEExactGauge.Target.WienerLaw)
    {n : ℕ} (hn : 3 ≤ n)
    (hm : 0 < SLEExactGauge.Target.moment κ W n)
    (hM : 0 < SLEExactGauge.Target.moment κ W (n + 1))
    (hi : Integrable (fun ω => Y ω ^ n) P)
    (hi' : Integrable (fun ω => Y ω ^ (n + 1)) P)
    (hretained : 3 * SLEExactGauge.Target.moment κ W n / 4 ≤ ∫ ω, Y ω ^ n ∂P)
    (hnext : (∫ ω, Y ω ^ (n + 1) ∂P) ≤ SLEExactGauge.Target.moment κ W (n + 1)) :
    (2 : ℝ) ^ n / 8 ≤ ∑' k : ℤ, (SLEExactGauge.Target.multiplicity κ W n k : ℝ) *
      P.real {ω | (2 : ℝ) ^ k ≤ Y ω} :=
  lower_batch_probability P Y hY hY0 hn hm hM hi hi' hretained hnext

lemma cleanup_count_le {x : ℝ} (hx : 0 ≤ x) (S : Finset ℕ) :
    ∑ n ∈ S, (if 16 * ((n : ℝ) + 1) ≤ x then (1 : ℝ) else 0) ≤ x / 16 := by
  classical
  rw [← Finset.sum_filter]
  let A : Finset ℕ := S.filter (fun n : ℕ => 16 * ((n : ℝ) + 1) ≤ x)
  have hsub : A ⊆ Finset.range ⌊x / 16⌋₊ := by
    intro n hn
    have hreal : (n : ℝ) + 1 ≤ x / 16 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).mpr
      simpa only [mul_comm] using (Finset.mem_filter.mp hn).2
    have hnat : n + 1 ≤ ⌊x / 16⌋₊ := Nat.le_floor (by simpa using hreal)
    exact Finset.mem_range.mpr (by omega)
  change (∑ n ∈ A, (1 : ℝ)) ≤ x / 16
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  calc
    (A.card : ℝ) ≤ (⌊x / 16⌋₊ : ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_range _)
    _ ≤ x / 16 := Nat.floor_le (by positivity)

/-- The cleanup entries have summable tail probabilities, bounded by the first
moment divided by 16. Indices `n + 1` are the paper's positive integers. -/
theorem cleanup_tail_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    (hX0 : ∀ ω, 0 ≤ X ω) (hi : Integrable X P) :
    Summable (fun n : ℕ => P.real {ω | 16 * ((n : ℝ) + 1) ≤ X ω}) ∧
      (∑' n : ℕ, P.real {ω | 16 * ((n : ℝ) + 1) ≤ X ω}) ≤ (∫ ω, X ω ∂P) / 16 := by
  classical
  have hsum (S : Finset ℕ) :
      ∑ n ∈ S, P.real {ω | 16 * ((n : ℝ) + 1) ≤ X ω} ≤ (∫ ω, X ω ∂P) / 16 := by
    have hset (n : ℕ) : MeasurableSet {ω | 16 * ((n : ℝ) + 1) ≤ X ω} :=
      measurableSet_le measurable_const hX
    have hcount (n : ℕ) : Integrable
        (fun ω => if 16 * ((n : ℝ) + 1) ≤ X ω then (1 : ℝ) else 0) P :=
      (integrable_const _).indicator (hset n)
    calc
      _ = ∫ ω, ∑ n ∈ S, if 16 * ((n : ℝ) + 1) ≤ X ω then (1 : ℝ) else 0 ∂P := by
        rw [integral_finsetSum S (fun n _ => hcount n)]
        apply Finset.sum_congr rfl
        intro n hn
        simpa only [Set.indicator, Set.mem_ofPred_eq, smul_eq_mul, mul_one] using
          (integral_indicator_const (μ := P) (1 : ℝ) (hset n)).symm
      _ ≤ ∫ ω, X ω / 16 ∂P := integral_mono
        (integrable_finsetSum S (fun n _ => hcount n)) (hi.div_const 16)
        (fun ω => cleanup_count_le (hX0 ω) S)
      _ = _ := integral_div _ _
  exact ⟨summable_of_sum_le (fun _ => measureReal_nonneg) hsum,
    Real.tsum_le_of_sum_le (fun _ => measureReal_nonneg) hsum⟩

lemma upper_constant_le_geometric {n : ℕ} (hn : 1 ≤ n) :
    (4 : ℝ) ^ n / 16 ^ n / (1 - (1 / 2 : ℝ) ^ n) ≤ 2 * (1 / 4 : ℝ) ^ n := by
  have hpow : (1 / 2 : ℝ) ^ n ≤ 1 / 2 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [pow_succ]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ (by norm_num) (by norm_num))
      (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans_eq (one_mul _)
  have he : (4 : ℝ) ^ n / 16 ^ n = (1 / 4 : ℝ) ^ n := by
    rw [← div_pow]
    norm_num
  rw [he]
  apply (div_le_iff₀ (denominator_pos hn)).mpr
  have hnonneg : 0 ≤ (1 / 4 : ℝ) ^ n := by positivity
  nlinarith

/-- Both types of entries in all positive-order batches have summable exceedance
probabilities. The hypotheses are precisely the positive finite moments of one
nonnegative mass, not any SLE conclusion. -/
theorem all_batch_tails_summable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    (hX0 : ∀ ω, 0 ≤ X ω) (m T : ℕ → ℝ)
    (hm : ∀ n, 1 ≤ n → 0 < m n)
    (hi : ∀ n, 1 ≤ n → Integrable (fun ω => X ω ^ n) P)
    (hMoment : ∀ n, 1 ≤ n → (∫ ω, X ω ^ n ∂P) = m n) :
    Summable (fun n : ℕ =>
      (∑' k : ℤ, (copies (n + 1) (m (n + 1)) (T (n + 1)) k : ℝ) *
        P.real {ω | 16 * dyadic k ≤ X ω}) +
      P.real {ω | 16 * ((n : ℝ) + 1) ≤ X ω}) := by
  have hgeom : Summable (fun n : ℕ => 2 * (1 / 4 : ℝ) ^ (n + 1)) := by
    simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
        (by norm_num : (1 / 4 : ℝ) < 1)).mul_left (2 * (1 / 4 : ℝ))
  have hbatch : Summable (fun n : ℕ =>
      ∑' k : ℤ, (copies (n + 1) (m (n + 1)) (T (n + 1)) k : ℝ) *
        P.real {ω | 16 * dyadic k ≤ X ω}) := by
    apply Summable.of_nonneg_of_le (fun n => tsum_nonneg (fun _ => by positivity)) _ hgeom
    intro n
    exact (upper_batch_probability P X hX hX0 (by omega) (hm _ (by omega))
      (hi _ (by omega)) (hMoment _ (by omega))).trans (upper_constant_le_geometric (by omega))
  have hfirst : Integrable X P := by simpa only [pow_one] using hi 1 le_rfl
  exact hbatch.add (cleanup_tail_bound P X hX hX0 hfirst).1

end SLEExactGauge.MomentBatches

end

end OAI
