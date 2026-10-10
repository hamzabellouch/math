import OAI.Combinatorics.BalancedRyser.Probability.PatternIntegrability

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace Balanced.PatternTails

variable (P : PatternModel)

theorem fixed_tail_le_moment (K : Finset P.Color) (x : P.Sample)
    (f : P.Sample → ℝ) (hf : Measurable f) (hf0 : ∀ ω, 0 ≤ f ω)
    (B : ℝ) (hfB : ∀ ω, f ω ≤ B) (t : ℝ) (ht : 0 < t) (n : ℕ) :
    P.measure.real {ω | t ≤ f (P.fixCoordinates K x ω)} ≤
      P.fixedExpectation K x (fun ω => f ω ^ n) / t ^ n := by
  have hi : Integrable (fun ω => f (P.fixCoordinates K x ω) ^ n) P.measure := by
    apply P.integrable_fixed_of_bound K x (hf.pow_const n) (B ^ n)
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hf0 ω) n)]
    exact pow_le_pow_left₀ (hf0 ω) (hfB ω) n
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => pow_nonneg (hf0 (P.fixCoordinates K x ω)) n))
    hi (t ^ n)
  have hsub : {ω | t ≤ f (P.fixCoordinates K x ω)} ⊆
      {ω | t ^ n ≤ f (P.fixCoordinates K x ω) ^ n} := by
    intro ω hω
    exact pow_le_pow_left₀ ht.le hω n
  apply (le_div_iff₀ (pow_pos ht n)).mpr
  calc
    P.measure.real {ω | t ≤ f (P.fixCoordinates K x ω)} * t ^ n ≤
        P.measure.real {ω | t ^ n ≤ f (P.fixCoordinates K x ω) ^ n} * t ^ n :=
      mul_le_mul_of_nonneg_right (measureReal_mono hsub) (pow_nonneg ht.le n)
    _ ≤ P.fixedExpectation K x (fun ω => f ω ^ n) := by
      simpa only [mul_comm, PatternModel.fixedExpectation] using hm

lemma count_mem_Icc (ω : P.Sample) :
    P.count ω ∈ Set.Icc (0 : ℝ) (Fintype.card P.Label : ℝ) := by
  constructor
  · exact Finset.sum_nonneg (fun a _ => P.indicator_nonneg a ω)
  · calc
      P.count ω ≤ ∑ _a : P.Label, (1 : ℝ) :=
        Finset.sum_le_sum (fun a _ => P.indicator_le_one a ω)
      _ = _ := by simp

lemma mean_mem_Icc (K : Finset P.Color) (x : P.Sample) :
    P.fixedExpectation K x P.count ∈ Set.Icc (0 : ℝ) (Fintype.card P.Label : ℝ) := by
  rw [P.fixedExpectation_count_eq_sum]
  constructor
  · exact Finset.sum_nonneg (fun a _ => P.fixedExpectation_indicator_nonneg K x a)
  · calc
      (∑ a, P.fixedExpectation K x (P.indicator a)) ≤ ∑ _a : P.Label, (1 : ℝ) :=
        Finset.sum_le_sum (fun a _ => P.fixedExpectation_indicator_le_one K x a)
      _ = _ := by simp

theorem count_tail_le (K : Finset P.Color) (x : P.Sample)
    (t : ℝ) (ht : 0 < t) (n : ℕ) :
    P.measure.real {ω | t ≤ P.count (P.fixCoordinates K x ω)} ≤
      P.fixedExpectation K x (fun ω => P.count ω ^ n) / t ^ n :=
  fixed_tail_le_moment P K x P.count P.measurable_count
    (fun ω => (count_mem_Icc P ω).1) (Fintype.card P.Label)
    (fun ω => (count_mem_Icc P ω).2) t ht n

theorem centered_tail_le (K : Finset P.Color) (x : P.Sample)
    (t : ℝ) (ht : 0 < t) (s : ℕ) :
    P.measure.real {ω | t ≤ |P.count (P.fixCoordinates K x ω) -
      P.fixedExpectation K x P.count|} ≤
      P.fixedExpectation K x
        (fun ω => |P.count ω - P.fixedExpectation K x P.count| ^ (2 * s)) /
          t ^ (2 * s) := by
  apply fixed_tail_le_moment P K x
    (fun ω => |P.count ω - P.fixedExpectation K x P.count|)
    ((P.measurable_count.sub_const _).abs) (fun ω => abs_nonneg _)
    (Fintype.card P.Label) _ t ht (2 * s)
  intro ω
  have hc := count_mem_Icc P ω
  have hm := mean_mem_Icc P K x
  exact abs_le.mpr ⟨by linarith [hc.1, hc.2, hm.1, hm.2],
    by linarith [hc.1, hc.2, hm.1, hm.2]⟩

end Balanced.PatternTails

namespace Balanced.PatternTails

theorem uniform_count_tail_of_moments
    (P : ℕ → PatternModel) (K : ∀ q, Finset (P q).Color)
    (hmom : UniformPatternMoments P K) (n : ℕ) (hn : 0 < n) :
    ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ, ∀ q, q₀ ≤ q → ∀ x : (P q).Sample,
      ∀ t : ℝ, 0 < t →
        (P q).measure.real {ω | t ≤ (P q).count ((P q).fixCoordinates (K q) x ω)} ≤
          C / t ^ n := by
  obtain ⟨C, hC, q₀, hq₀⟩ := hmom n hn
  refine ⟨C, hC, q₀, ?_⟩
  intro q hq x t ht
  exact (count_tail_le (P q) (K q) x t ht n).trans
    (div_le_div_of_nonneg_right (hq₀ q hq x) (pow_nonneg ht.le n))

theorem uniform_centered_linear_tail_of_moments
    (P : ℕ → PatternModel) (K : ∀ q, Finset (P q).Color)
    (hmom : UniformCenteredPatternMoments P K)
    (s : ℕ) (hs : 0 < s) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ, ∀ q, q₀ ≤ q → ∀ x : (P q).Sample,
      (P q).measure.real {ω | ε * (q : ℝ) ≤
        |(P q).count ((P q).fixCoordinates (K q) x ω) -
          (P q).fixedExpectation (K q) x (P q).count|} ≤ C / (q : ℝ) ^ s := by
  obtain ⟨C, hC, q₀, hq₀⟩ := hmom s hs
  refine ⟨C / ε ^ (2 * s), div_pos hC (pow_pos hε _), max q₀ 1, ?_⟩
  intro q hq x
  have hq0 : q₀ ≤ q := (le_max_left _ _).trans hq
  have hqpos : (0 : ℝ) < q := by
    have : 1 ≤ q := (le_max_right q₀ 1).trans hq
    exact_mod_cast (by omega : 0 < q)
  calc
    (P q).measure.real {ω | ε * (q : ℝ) ≤
      |(P q).count ((P q).fixCoordinates (K q) x ω) -
        (P q).fixedExpectation (K q) x (P q).count|} ≤
      (P q).fixedExpectation (K q) x
        (fun ω => |(P q).count ω - (P q).fixedExpectation (K q) x (P q).count| ^
          (2 * s)) / (ε * q) ^ (2 * s) :=
        centered_tail_le (P q) (K q) x (ε * q) (mul_pos hε hqpos) s
    _ ≤ (C * q ^ s) / (ε * q) ^ (2 * s) :=
      div_le_div_of_nonneg_right (hq₀ q hq0 x) (pow_nonneg (mul_pos hε hqpos).le _)
    _ = (C / ε ^ (2 * s)) / (q : ℝ) ^ s := by
      rw [mul_pow, show 2 * s = s + s by omega, pow_add, pow_add]
      field_simp

theorem finite_fixed_tail_union_le
    (P : PatternModel) (K : Finset P.Color) (x : P.Sample)
    {ι : Type*} [Fintype ι] (f : ι → P.Sample → ℝ)
    (hf : ∀ i, Measurable (f i)) (hf0 : ∀ i ω, 0 ≤ f i ω)
    (B : ι → ℝ) (hfB : ∀ i ω, f i ω ≤ B i)
    (t C : ℝ) (ht : 0 < t) (n : ℕ)
    (hmom : ∀ i, P.fixedExpectation K x (fun ω => f i ω ^ n) ≤ C) :
    P.measure.real {ω | ∃ i, t ≤ f i (P.fixCoordinates K x ω)} ≤
      (Fintype.card ι : ℝ) * (C / t ^ n) := by
  classical
  have hset : {ω | ∃ i, t ≤ f i (P.fixCoordinates K x ω)} =
      ⋃ i, {ω | t ≤ f i (P.fixCoordinates K x ω)} := by ext ω; simp
  rw [hset]
  calc
    P.measure.real (⋃ i, {ω | t ≤ f i (P.fixCoordinates K x ω)}) ≤
        ∑ i, P.measure.real {ω | t ≤ f i (P.fixCoordinates K x ω)} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : ι, C / t ^ n := Finset.sum_le_sum (fun i _ =>
      (fixed_tail_le_moment P K x (f i) (hf i) (hf0 i) (B i) (hfB i) t ht n).trans
        (div_le_div_of_nonneg_right (hmom i) (pow_nonneg ht.le n)))
    _ = _ := by simp

end Balanced.PatternTails

namespace Balanced.PatternTails

theorem uniform_count_oneHundredth_tail_of_moments
    (P : ℕ → PatternModel) (K : ∀ q, Finset (P q).Color)
    (hmom : UniformPatternMoments P K) (k : ℕ) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ, ∀ q, q₀ ≤ q → ∀ x : (P q).Sample,
      (P q).measure.real {ω | (q : ℝ) ^ ((1 : ℝ) / 100) ≤
        (P q).count ((P q).fixCoordinates (K q) x ω)} ≤ C / (q : ℝ) ^ k := by
  obtain ⟨C, hC, q₀, hq₀⟩ :=
    uniform_count_tail_of_moments P K hmom (100 * k) (by omega)
  refine ⟨C, hC, max q₀ 1, ?_⟩
  intro q hq x
  have hqpos : (0 : ℝ) < q := by
    have : 1 ≤ q := (le_max_right q₀ 1).trans hq
    exact_mod_cast (by omega : 0 < q)
  have hpow : ((q : ℝ) ^ ((1 : ℝ) / 100)) ^ (100 * k) = (q : ℝ) ^ k := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg q)]
    have he : ((1 : ℝ) / 100) * ((100 * k : ℕ) : ℝ) = (k : ℝ) := by
      push_cast
      ring
    rw [he, Real.rpow_natCast]
  simpa only [hpow] using hq₀ q ((le_max_left q₀ 1).trans hq) x
    ((q : ℝ) ^ ((1 : ℝ) / 100)) (Real.rpow_pos_of_pos hqpos _)

end Balanced.PatternTails

end OAI
