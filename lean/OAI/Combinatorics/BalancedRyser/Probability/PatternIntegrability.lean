import OAI.Combinatorics.BalancedRyser.Probability.PatternMomentsLemmas

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace Balanced.PatternModel

variable (P : PatternModel)

instance isProbabilityMeasure_measure : IsProbabilityMeasure P.measure := by
  unfold measure
  infer_instance

lemma measurable_fixCoordinates (K : Finset P.Color) (x : P.Sample) :
    Measurable (P.fixCoordinates K x) := by
  classical
  apply Measurable.of_eval
  intro c
  by_cases hc : c ∈ K
  · simp [fixCoordinates, hc]
  · simpa [fixCoordinates, hc] using (measurable_pi_apply c)

lemma measurable_indicator (a : P.Label) : Measurable (P.indicator a) :=
  measurable_const.indicator (P.eventMeasurable a)

lemma indicator_nonneg (a : P.Label) (ω : P.Sample) : 0 ≤ P.indicator a ω := by
  classical
  simp only [indicator, Set.indicator_apply]
  split_ifs <;> norm_num

lemma indicator_le_one (a : P.Label) (ω : P.Sample) : P.indicator a ω ≤ 1 := by
  classical
  simp only [indicator, Set.indicator_apply]
  split_ifs <;> norm_num

lemma measurable_count : Measurable P.count := by
  classical
  exact Finset.measurable_sum _ fun a _ => P.measurable_indicator a

lemma integrable_fixed_of_bound (K : Finset P.Color) (x : P.Sample)
    {f : P.Sample → ℝ} (hf : Measurable f) (C : ℝ)
    (hC : ∀ ω, ‖f ω‖ ≤ C) :
    Integrable (fun ω => f (P.fixCoordinates K x ω)) P.measure := by
  exact Integrable.of_bound
    (hf.comp (P.measurable_fixCoordinates K x)).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ω => hC _)

lemma integrable_fixed_indicator (K : Finset P.Color) (x : P.Sample) (a : P.Label) :
    Integrable (fun ω => P.indicator a (P.fixCoordinates K x ω)) P.measure := by
  apply P.integrable_fixed_of_bound K x (P.measurable_indicator a) 1
  intro ω
  simpa only [Real.norm_eq_abs, abs_of_nonneg (P.indicator_nonneg a ω)] using
    P.indicator_le_one a ω

lemma fixedExpectation_nonneg (K : Finset P.Color) (x : P.Sample)
    {f : P.Sample → ℝ} (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ P.fixedExpectation K x f :=
  integral_nonneg fun _ => hf _

@[simp] lemma fixedExpectation_const (K : Finset P.Color) (x : P.Sample) (c : ℝ) :
    P.fixedExpectation K x (fun _ => c) = c := by
  simp [fixedExpectation]

lemma fixedExpectation_indicator_nonneg (K : Finset P.Color) (x : P.Sample) (a : P.Label) :
    0 ≤ P.fixedExpectation K x (P.indicator a) :=
  P.fixedExpectation_nonneg K x (P.indicator_nonneg a)

lemma fixedExpectation_indicator_le_one (K : Finset P.Color) (x : P.Sample) (a : P.Label) :
    P.fixedExpectation K x (P.indicator a) ≤ 1 := by
  calc
    P.fixedExpectation K x (P.indicator a) ≤ P.fixedExpectation K x (fun _ => 1) := by
      apply integral_mono (P.integrable_fixed_indicator K x a) (integrable_const 1)
      intro ω
      exact P.indicator_le_one a _
    _ = 1 := P.fixedExpectation_const K x 1

noncomputable def positiveProduct (K₀ : Finset P.Color) (x : P.Sample)
    (as : List P.Label) (ω : P.Sample) : ℝ :=
  (as.map fun a => P.indicator a ω + P.fixedExpectation K₀ x (P.indicator a)).prod

noncomputable def centeredProduct (K₀ : Finset P.Color) (x : P.Sample)
    (as : List P.Label) (ω : P.Sample) : ℝ :=
  (as.map fun a => P.indicator a ω - P.fixedExpectation K₀ x (P.indicator a)).prod

noncomputable def productWeight (K₀ : Finset P.Color) (x : P.Sample)
    (as : List P.Label) : ℝ :=
  P.fixedExpectation K₀ x (P.positiveProduct K₀ x as)

lemma positiveProduct_nonneg (K₀ : Finset P.Color) (x : P.Sample)
    (as : List P.Label) (ω : P.Sample) : 0 ≤ P.positiveProduct K₀ x as ω := by
  apply List.prod_nonneg
  intro t ht
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp ht
  exact add_nonneg (P.indicator_nonneg a ω) (P.fixedExpectation_indicator_nonneg K₀ x a)

lemma positiveProduct_le (K₀ : Finset P.Color) (x : P.Sample)
    (as : List P.Label) (ω : P.Sample) : P.positiveProduct K₀ x as ω ≤ 2 ^ as.length := by
  induction as with
  | nil => simp [positiveProduct]
  | cons a as ih =>
    simp only [positiveProduct, List.map_cons, List.prod_cons, List.length_cons]
    rw [pow_succ']
    apply mul_le_mul _ ih (P.positiveProduct_nonneg K₀ x as ω) (by norm_num)
    have h₁ := P.indicator_le_one a ω
    have h₂ := P.fixedExpectation_indicator_le_one K₀ x a
    linarith

lemma measurable_positiveProduct (K₀ : Finset P.Color) (x : P.Sample)
    (as : List P.Label) : Measurable (P.positiveProduct K₀ x as) := by
  induction as with
  | nil => exact measurable_const
  | cons a as ih =>
    exact ((P.measurable_indicator a).add measurable_const).mul ih

lemma measurable_centeredProduct (K₀ : Finset P.Color) (x : P.Sample)
    (as : List P.Label) : Measurable (P.centeredProduct K₀ x as) := by
  induction as with
  | nil => exact measurable_const
  | cons a as ih =>
    exact ((P.measurable_indicator a).sub measurable_const).mul ih

lemma abs_centeredProduct_le (K₀ : Finset P.Color) (x : P.Sample)
    (as : List P.Label) (ω : P.Sample) :
    |P.centeredProduct K₀ x as ω| ≤ P.positiveProduct K₀ x as ω := by
  induction as with
  | nil => simp [centeredProduct, positiveProduct]
  | cons a as ih =>
    simp only [centeredProduct, positiveProduct, List.map_cons, List.prod_cons, abs_mul]
    apply mul_le_mul _ ih (abs_nonneg _) (add_nonneg (P.indicator_nonneg a ω)
      (P.fixedExpectation_indicator_nonneg K₀ x a))
    rw [abs_sub_le_iff]
    constructor <;> linarith [P.indicator_nonneg a ω,
      P.fixedExpectation_indicator_nonneg K₀ x a]

lemma integrable_fixed_positiveProduct (K₀ K : Finset P.Color) (x y : P.Sample)
    (as : List P.Label) :
    Integrable (fun ω => P.positiveProduct K₀ x as (P.fixCoordinates K y ω)) P.measure := by
  apply P.integrable_fixed_of_bound K y (P.measurable_positiveProduct K₀ x as) (2 ^ as.length)
  intro ω
  simpa only [Real.norm_eq_abs, abs_of_nonneg (P.positiveProduct_nonneg K₀ x as ω)] using
    P.positiveProduct_le K₀ x as ω

lemma integrable_fixed_centeredProduct (K₀ K : Finset P.Color) (x y : P.Sample)
    (as : List P.Label) :
    Integrable (fun ω => P.centeredProduct K₀ x as (P.fixCoordinates K y ω)) P.measure := by
  apply P.integrable_fixed_of_bound K y (P.measurable_centeredProduct K₀ x as) (2 ^ as.length)
  intro ω
  exact (P.abs_centeredProduct_le K₀ x as ω).trans (P.positiveProduct_le K₀ x as ω)

lemma productWeight_nonneg (K₀ : Finset P.Color) (x : P.Sample) (as : List P.Label) :
    0 ≤ P.productWeight K₀ x as :=
  P.fixedExpectation_nonneg K₀ x (P.positiveProduct_nonneg K₀ x as)

@[simp] lemma productWeight_nil (K₀ : Finset P.Color) (x : P.Sample) :
    P.productWeight K₀ x [] = 1 := by
  change P.fixedExpectation K₀ x (fun _ => (1 : ℝ)) = 1
  exact P.fixedExpectation_const K₀ x 1

lemma positiveProduct_perm (K₀ : Finset P.Color) (x : P.Sample)
    {as bs : List P.Label} (h : as.Perm bs) :
    P.positiveProduct K₀ x as = P.positiveProduct K₀ x bs := by
  funext ω
  exact (h.map _).prod_eq

lemma centeredProduct_perm (K₀ : Finset P.Color) (x : P.Sample)
    {as bs : List P.Label} (h : as.Perm bs) :
    P.centeredProduct K₀ x as = P.centeredProduct K₀ x bs := by
  funext ω
  exact (h.map _).prod_eq

lemma productWeight_perm (K₀ : Finset P.Color) (x : P.Sample)
    {as bs : List P.Label} (h : as.Perm bs) :
    P.productWeight K₀ x as = P.productWeight K₀ x bs := by
  unfold productWeight
  rw [P.positiveProduct_perm K₀ x h]

lemma abs_fixedExpectation_centeredProduct_le (K₀ : Finset P.Color) (x : P.Sample)
    (as : List P.Label) :
    |P.fixedExpectation K₀ x (P.centeredProduct K₀ x as)| ≤ P.productWeight K₀ x as := by
  unfold productWeight fixedExpectation
  simpa only [Real.norm_eq_abs] using
    (norm_integral_le_of_norm_le
      (f := fun ω => P.centeredProduct K₀ x as (P.fixCoordinates K₀ x ω))
      (P.integrable_fixed_positiveProduct K₀ K₀ x x as)
      (Filter.Eventually.of_forall fun ω => by
        simpa only [Real.norm_eq_abs] using
          P.abs_centeredProduct_le K₀ x as (P.fixCoordinates K₀ x ω)))

lemma indicator_eq_of_agree (a : P.Label) (ω η : P.Sample)
    (h : ∀ c ∈ P.support a, ω c = η c) : P.indicator a ω = P.indicator a η := by
  classical
  have he := P.dependsOn a ω η h
  by_cases hω : ω ∈ P.event a
  · have hη := he.mp hω
    simp [indicator, hω, hη]
  · have hη : η ∉ P.event a := fun hη => hω (he.mpr hη)
    simp [indicator, hω, hη]

lemma positiveProduct_eq_of_agree (K₀ : Finset P.Color) (x : P.Sample)
    (as : List P.Label) (ω η : P.Sample)
    (h : ∀ a ∈ as, ∀ c ∈ P.support a, ω c = η c) :
    P.positiveProduct K₀ x as ω = P.positiveProduct K₀ x as η := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    change (P.indicator a ω + _) * P.positiveProduct K₀ x as ω =
      (P.indicator a η + _) * P.positiveProduct K₀ x as η
    rw [P.indicator_eq_of_agree a ω η (h a (by simp))]
    rw [ih (fun b hb => h b (by simp [hb]))]

lemma centeredProduct_eq_of_agree (K₀ : Finset P.Color) (x : P.Sample)
    (as : List P.Label) (ω η : P.Sample)
    (h : ∀ a ∈ as, ∀ c ∈ P.support a, ω c = η c) :
    P.centeredProduct K₀ x as ω = P.centeredProduct K₀ x as η := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    change (P.indicator a ω - _) * P.centeredProduct K₀ x as ω =
      (P.indicator a η - _) * P.centeredProduct K₀ x as η
    rw [P.indicator_eq_of_agree a ω η (h a (by simp))]
    rw [ih (fun b hb => h b (by simp [hb]))]

noncomputable def additionalSupport (K₀ : Finset P.Color) (as : List P.Label) : Finset P.Color :=
  by
    classical
    exact as.toFinset.biUnion (fun a => P.support a \ K₀)

lemma positiveProduct_dependsOn (K₀ : Finset P.Color) (x : P.Sample)
    (as : List P.Label) (ω η : P.Sample)
    (h : ∀ c ∈ K₀ ∪ P.additionalSupport K₀ as, ω c = η c) :
    P.positiveProduct K₀ x as ω = P.positiveProduct K₀ x as η := by
  classical
  apply P.positiveProduct_eq_of_agree K₀ x as ω η
  intro a ha c hc
  apply h c
  by_cases hc₀ : c ∈ K₀
  · exact Finset.mem_union_left _ hc₀
  · apply Finset.mem_union_right
    simp only [additionalSupport, Finset.mem_biUnion, List.mem_toFinset, Finset.mem_sdiff]
    exact ⟨a, ha, hc, hc₀⟩

lemma centeredProduct_dependsOn (K₀ : Finset P.Color) (x : P.Sample)
    (as : List P.Label) (ω η : P.Sample)
    (h : ∀ c ∈ K₀ ∪ P.additionalSupport K₀ as, ω c = η c) :
    P.centeredProduct K₀ x as ω = P.centeredProduct K₀ x as η := by
  classical
  apply P.centeredProduct_eq_of_agree K₀ x as ω η
  intro a ha c hc
  apply h c
  by_cases hc₀ : c ∈ K₀
  · exact Finset.mem_union_left _ hc₀
  · apply Finset.mem_union_right
    simp only [additionalSupport, Finset.mem_biUnion, List.mem_toFinset, Finset.mem_sdiff]
    exact ⟨a, ha, hc, hc₀⟩

lemma fixedExpectation_count_eq_sum (K : Finset P.Color) (x : P.Sample) :
    P.fixedExpectation K x P.count = ∑ a, P.fixedExpectation K x (P.indicator a) := by
  classical
  unfold fixedExpectation count
  exact integral_finsetSum _ (fun a _ => P.integrable_fixed_indicator K x a)

lemma sum_centered_indicators (K : Finset P.Color) (x ω : P.Sample) :
    (∑ a, (P.indicator a ω - P.fixedExpectation K x (P.indicator a))) =
      P.count ω - P.fixedExpectation K x P.count := by
  classical
  rw [Finset.sum_sub_distrib, P.fixedExpectation_count_eq_sum]
  rfl

end Balanced.PatternModel

end OAI
