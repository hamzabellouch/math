import Mathlib

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.StaticCertificates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
noncomputable def poissonLaw (rate : ι → ℝ≥0) : Measure (ι → ℕ) :=
  Measure.pi (fun i => poissonMeasure (rate i))

instance flat_HighMomentRecovered_3 (rate : ι → ℝ≥0) : IsProbabilityMeasure (poissonLaw rate) := by
  unfold poissonLaw
  infer_instance

def positiveEvent (C : Finset ι) : Set (ι → ℕ) :=
  (C : Set ι).pi (fun _ => ({0} : Set ℕ)ᶜ)

noncomputable def certificateIndicator (C : Finset ι) (ω : ι → ℕ) : ℝ :=
  (positiveEvent C).indicator (fun _ => 1) ω

noncomputable def weight (rate : ι → ℝ≥0) (C : Finset ι) : ℝ :=
  ∏ i ∈ C, (rate i : ℝ)

omit [Fintype ι] [DecidableEq ι] in
lemma measurableSet_positiveEvent (C : Finset ι) : MeasurableSet (positiveEvent C) :=
  MeasurableSet.pi C.finite_toSet.countable (fun _ _ => (measurableSet_singleton 0).compl)
omit [DecidableEq ι] in

lemma integrable_certificateIndicator (rate : ι → ℝ≥0) (C : Finset ι) :
    Integrable (certificateIndicator C) (poissonLaw rate) :=
  (integrable_const (1 : ℝ)).indicator (measurableSet_positiveEvent C)

omit [Fintype ι] [DecidableEq ι] in
lemma indicator_nonneg (C : Finset ι) (ω : ι → ℕ) :
    0 ≤ certificateIndicator C ω := by
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
omit [DecidableEq ι] in

lemma integral_certificateIndicator (rate : ι → ℝ≥0) (C : Finset ι) :
    (∫ ω, certificateIndicator C ω ∂poissonLaw rate) =
      ∏ i ∈ C, (1 - Real.exp (-(rate i : ℝ))) := by
  unfold certificateIndicator
  rw [integral_indicator_const _ (measurableSet_positiveEvent C)]
  simp only [smul_eq_mul, mul_one]
  rw [Measure.real, poissonLaw, positiveEvent, Measure.pi_pi_finset,
    ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Measure.real, measureReal_compl (measurableSet_singleton 0),
    probReal_univ, Measure.real, poissonMeasure_singleton]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
omit [DecidableEq ι] in

lemma integral_certificateIndicator_le (rate : ι → ℝ≥0) (C : Finset ι) :
    (∫ ω, certificateIndicator C ω ∂poissonLaw rate) ≤ weight rate C := by
  rw [integral_certificateIndicator]
  apply Finset.prod_le_prod₀
  · intro i _
    have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (rate i).coe_nonneg)
    linarith
  · intro i _
    have he := Real.add_one_le_exp (-(rate i : ℝ))
    linarith

omit [Fintype ι] [DecidableEq ι] in
lemma weight_nonneg (rate : ι → ℝ≥0) (C : Finset ι) : 0 ≤ weight rate C := by
  exact Finset.prod_nonneg (fun i _ => (rate i).coe_nonneg)

omit [Fintype ι] in

lemma weight_union (rate : ι → ℝ≥0) (C D : Finset ι) :
    weight rate (C ∪ D) = weight rate C * weight rate (D \ C) := by
  unfold weight
  rw [← Finset.prod_union (Finset.disjoint_sdiff)]
  congr 1
  ext i
  simp only [Finset.mem_union, Finset.mem_sdiff]
  tauto

omit [Fintype ι] in
lemma positiveEvent_union (C D : Finset ι) :
    positiveEvent (C ∪ D) = positiveEvent C ∩ positiveEvent D := by
  ext ω
  simp [positiveEvent, Set.mem_pi, or_imp, forall_and]

omit [DecidableEq ι] in

theorem static_union_bound {κ : Type*} (D : Finset κ) (requirements : κ → Finset ι)
    (rate : ι → ℝ≥0) (E : Set (ι → ℕ)) (hE : MeasurableSet E)
    (hcover : ∀ ω ∈ E, ∃ c ∈ D, ω ∈ positiveEvent (requirements c)) :
    (poissonLaw rate).real E ≤ ∑ c ∈ D, weight rate (requirements c) := by
  have hp (ω : ι → ℕ) : E.indicator (fun _ => (1 : ℝ)) ω ≤
      ∑ c ∈ D, certificateIndicator (requirements c) ω := by
    by_cases hω : ω ∈ E
    · obtain ⟨c, hc, he⟩ := hcover ω hω
      have := Finset.single_le_sum (f := fun c => certificateIndicator (requirements c) ω)
        (fun c _ => indicator_nonneg _ _) hc
      simpa [certificateIndicator, he, hω] using this
    · simp only [Set.indicator_of_notMem hω]
      exact Finset.sum_nonneg (fun c _ => indicator_nonneg _ _)
  calc
    _ = ∫ ω, E.indicator (fun _ => (1 : ℝ)) ω ∂poissonLaw rate := by
      rw [integral_indicator_const _ hE]
      simp
    _ ≤ ∫ ω, ∑ c ∈ D, certificateIndicator (requirements c) ω ∂poissonLaw rate :=
      integral_mono ((integrable_const (1 : ℝ)).indicator hE)
        (integrable_finsetSum _ (fun c _ => integrable_certificateIndicator _ _)) hp
    _ = ∑ c ∈ D, ∫ ω, certificateIndicator (requirements c) ω ∂poissonLaw rate :=
      integral_finsetSum _ (fun c _ => integrable_certificateIndicator _ _)
    _ ≤ _ := Finset.sum_le_sum (fun c _ => integral_certificateIndicator_le _ _)

section PairWitnesses

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def witnessRequirements (T : Finset κ) (S : Finset ι) (f : T → S) : Finset (κ × ι) :=
  T.attach.image (fun r => (r.val, (f r).val))

omit [Fintype ι] [Fintype κ] in
lemma witnessRequirements_card (T : Finset κ) (S : Finset ι) (f : T → S) :
    (witnessRequirements T S f).card = T.card := by
  rw [witnessRequirements, Finset.card_image_of_injective]
  · exact Finset.card_attach
  · intro a b h
    exact Subtype.ext (congrArg Prod.fst h)

omit [Fintype ι] [Fintype κ] in
lemma witness_weight (rate : ι → ℝ≥0) (T : Finset κ) (S : Finset ι) (f : T → S) :
    weight (fun p : κ × ι => rate p.2) (witnessRequirements T S f) =
      ∏ r : T, (rate (f r) : ℝ) := by
  unfold weight witnessRequirements
  rw [Finset.prod_image]
  · rw [Finset.univ_eq_attach T]
  · intro a _ b _ h
    exact Subtype.ext (congrArg Prod.fst h)
omit [Fintype ι] [Fintype κ] in

lemma sum_witness_weight (rate : ι → ℝ≥0) (T : Finset κ) (S : Finset ι) :
    (∑ f : T → S, weight (fun p : κ × ι => rate p.2) (witnessRequirements T S f)) =
      (∑ i ∈ S, (rate i : ℝ)) ^ T.card := by
  simp_rw [witness_weight]
  rw [← Fintype.prod_sum (fun (_r : T) (i : S) => (rate i : ℝ))]
  rw [Finset.sum_coe_sort S (fun i => (rate i : ℝ))]
  simp

omit [Fintype ι] in

theorem pair_certificate_weight (rate : ι → ℝ≥0) (S : Finset ι) (K : ℕ) :
    (∑ T ∈ (Finset.univ : Finset κ).powersetCard K,
      ∑ f : T → S, weight (fun p : κ × ι => rate p.2) (witnessRequirements T S f)) =
      (Fintype.card κ).choose K * (∑ i ∈ S, (rate i : ℝ)) ^ K := by
  simp_rw [sum_witness_weight]
  calc
    _ = ∑ _T ∈ (Finset.univ : Finset κ).powersetCard K,
        (∑ i ∈ S, (rate i : ℝ)) ^ K := by
      apply Finset.sum_congr rfl
      intro T hT
      rw [(Finset.mem_powersetCard.mp hT).2]
    _ = _ := by simp

omit [Fintype ι] in

theorem pair_certificate_weight_le (rate : ι → ℝ≥0) (S : Finset ι) (K : ℕ) :
    (∑ T ∈ (Finset.univ : Finset κ).powersetCard K,
      ∑ f : T → S, weight (fun p : κ × ι => rate p.2) (witnessRequirements T S f)) ≤
        ((Fintype.card κ : ℝ) * ∑ i ∈ S, (rate i : ℝ)) ^ K := by
  rw [pair_certificate_weight, mul_pow]
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast Nat.choose_le_pow (Fintype.card κ) K
  · positivity

omit [Fintype ι] [Fintype κ] in

theorem pair_witness_exists (S : Finset ι) (T : Finset κ) (ω : κ × ι → ℕ)
    (hT : ∀ r ∈ T, ∃ i ∈ S, ω (r, i) ≠ 0) :
    ∃ f : T → S, ω ∈ positiveEvent (witnessRequirements T S f) := by
  classical
  have h (r : T) : ∃ i : S, ω (r.val, i.val) ≠ 0 := by
    obtain ⟨i, hi, he⟩ := hT r r.property
    exact ⟨⟨i, hi⟩, he⟩
  choose f hf using h
  refine ⟨f, ?_⟩
  intro p hp
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hp
  exact hf r

def dictionary (C : Finset (κ × ι)) : Finset ι := C.image Prod.snd

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
lemma direction_mem_dictionary {C : Finset (κ × ι)} {r : κ} {i : ι}
    (h : (r, i) ∈ C) : i ∈ dictionary C := Finset.mem_image_of_mem _ h
omit [Fintype ι] [Fintype κ] in

lemma witnessRequirements_disjoint {C : Finset (κ × ι)} (T : Finset κ) (S : Finset ι)
    (f : T → S) (hnew : Disjoint S (dictionary C)) :
    Disjoint C (witnessRequirements T S f) := by
  apply Finset.disjoint_left.mpr
  intro p hp hp'
  obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hp'
  have he := congrArg Prod.snd hr
  have hf : p.2 ∈ S := he ▸ (f r).property
  exact Finset.disjoint_left.mp hnew hf (direction_mem_dictionary hp)

omit [Fintype ι] [Fintype κ] in
lemma weight_union_fresh (rate : κ × ι → ℝ≥0) (C D : Finset (κ × ι))
    (hfresh : Disjoint C D) : weight rate (C ∪ D) = weight rate C * weight rate D := by
  exact Finset.prod_union hfresh

omit [Fintype ι] [Fintype κ] in

theorem pair_dictionary_extension (rate : ι → ℝ≥0) (C : Finset (κ × ι))
    (T : Finset κ) (S : Finset ι) (f : T → S) (hnew : Disjoint S (dictionary C)) :
    weight (fun p : κ × ι => rate p.2) (C ∪ witnessRequirements T S f) =
      weight (fun p : κ × ι => rate p.2) C * ∏ r : T, (rate (f r) : ℝ) := by
  rw [weight_union_fresh _ _ _ (witnessRequirements_disjoint T S f hnew), witness_weight]

def anchorRequirements (C : Finset (κ × ι)) (r : κ) (i : ι) : Finset (κ × ι) :=
  if i ∈ dictionary C then ∅ else {(r, i)}
omit [Fintype ι] [Fintype κ] [DecidableEq κ] in

lemma anchorRequirements_disjoint (C : Finset (κ × ι)) (r : κ) (i : ι) :
    Disjoint C (anchorRequirements C r i) := by
  unfold anchorRequirements
  split_ifs with h
  · exact Finset.disjoint_empty_right _
  · simp only [Finset.disjoint_singleton_right]
    exact fun hi => h (direction_mem_dictionary hi)

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
lemma anchorRequirements_weight (rate : ι → ℝ≥0) (C : Finset (κ × ι))
    (r : κ) (i : ι) :
    weight (fun p : κ × ι => rate p.2) (anchorRequirements C r i) =
      if i ∈ dictionary C then 1 else (rate i : ℝ) := by
  unfold anchorRequirements weight
  split_ifs <;> simp
omit [Fintype ι] [Fintype κ] in

lemma anchor_dictionary_extension (rate : ι → ℝ≥0) (C : Finset (κ × ι))
    (r : κ) (i : ι) :
    weight (fun p : κ × ι => rate p.2) (C ∪ anchorRequirements C r i) =
      weight (fun p : κ × ι => rate p.2) C *
        (if i ∈ dictionary C then 1 else (rate i : ℝ)) := by
  rw [weight_union_fresh _ _ _ (anchorRequirements_disjoint C r i), anchorRequirements_weight]
omit [Fintype ι] [Fintype κ] in

lemma anchor_dictionary_subset (C : Finset (κ × ι)) (r : κ) (i : ι) :
    dictionary (C ∪ anchorRequirements C r i) ⊆ insert i (dictionary C) := by
  intro d hd
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
  rcases Finset.mem_union.mp hp with hp | hp
  · exact Finset.mem_insert_of_mem (direction_mem_dictionary hp)
  · unfold anchorRequirements at hp
    split_ifs at hp with h
    · simp at hp
    · have he := Finset.mem_singleton.mp hp
      rw [he]
      exact Finset.mem_insert_self _ _

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in

lemma old_reference_has_hit (C : Finset (κ × ι)) (i : ι) (hi : i ∈ dictionary C)
    (ω : (κ × ι) → ℕ) (hω : ω ∈ positiveEvent C) : ∃ r, ω (r, i) ≠ 0 := by
  obtain ⟨p, hp, hpi⟩ := Finset.mem_image.mp hi
  refine ⟨p.1, ?_⟩
  have hh := hω p hp
  simpa [← hpi] using hh

omit [Fintype ι] [DecidableEq κ] in

theorem anchor_choice_weight_le (rate : ι → ℝ≥0) (C : Finset (κ × ι)) (S : Finset ι) :
    (∑ _i ∈ S ∩ dictionary C, (1 : ℝ)) +
        (∑ _r : κ, ∑ i ∈ S \ dictionary C, (rate i : ℝ)) ≤
      (dictionary C).card + Fintype.card κ * ∑ i ∈ S, (rate i : ℝ) := by
  apply add_le_add
  · simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_right (s₁ := S))
  · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
      (by intro i _ _; exact (rate i).coe_nonneg)

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
lemma dictionary_card_le (C : Finset (κ × ι)) : (dictionary C).card ≤ C.card :=
  Finset.card_image_le

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
lemma anchorRequirements_card_le (C : Finset (κ × ι)) (r : κ) (i : ι) :
    (anchorRequirements C r i).card ≤ 1 := by
  unfold anchorRequirements
  split_ifs <;> simp
omit [Fintype ι] [Fintype κ] in

lemma anchor_extension_card (C : Finset (κ × ι)) (r : κ) (i : ι) :
    (C ∪ anchorRequirements C r i).card ≤ C.card + 1 :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add_left (anchorRequirements_card_le C r i) _)
omit [Fintype ι] [Fintype κ] in

lemma pair_extension_card (C : Finset (κ × ι)) (T : Finset κ) (S : Finset ι) (f : T → S) :
    (C ∪ witnessRequirements T S f).card ≤ C.card + T.card := by
  simpa only [witnessRequirements_card] using Finset.card_union_le C (witnessRequirements T S f)

abbrev AnchorChoice (C : Finset (κ × ι)) (S : Finset ι) :=
  {i // i ∈ S ∩ dictionary C} ⊕ (κ × {i // i ∈ S \ dictionary C})

def AnchorChoice.direction {C : Finset (κ × ι)} {S : Finset ι} : AnchorChoice C S → ι
  | .inl d => d.val
  | .inr rd => rd.2.val

def AnchorChoice.requirements {C : Finset (κ × ι)} {S : Finset ι} :
    AnchorChoice C S → Finset (κ × ι)
  | .inl _ => ∅
  | .inr rd => {(rd.1, rd.2.val)}

noncomputable def AnchorChoice.cost (rate : ι → ℝ≥0)
    {C : Finset (κ × ι)} {S : Finset ι} : AnchorChoice C S → ℝ
  | .inl _ => 1
  | .inr rd => rate rd.2.val

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
lemma AnchorChoice.cost_nonneg (rate : ι → ℝ≥0)
    {C : Finset (κ × ι)} {S : Finset ι} (x : AnchorChoice C S) : 0 ≤ x.cost rate := by
  cases x <;> simp [AnchorChoice.cost]

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
lemma AnchorChoice.direction_mem {C : Finset (κ × ι)} {S : Finset ι}
    (x : AnchorChoice C S) : x.direction ∈ S := by
  cases x with
  | inl d => exact (Finset.mem_inter.mp d.property).1
  | inr rd => exact (Finset.mem_sdiff.mp rd.2.property).1
omit [Fintype ι] [Fintype κ] [DecidableEq κ] in

lemma AnchorChoice.fresh {C : Finset (κ × ι)} {S : Finset ι}
    (x : AnchorChoice C S) : Disjoint C x.requirements := by
  cases x with
  | inl d => exact Finset.disjoint_empty_right _
  | inr rd =>
    apply Finset.disjoint_singleton_right.mpr
    intro he
    exact (Finset.mem_sdiff.mp rd.2.property).2 (direction_mem_dictionary he)

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
lemma AnchorChoice.weight (rate : ι → ℝ≥0)
    {C : Finset (κ × ι)} {S : Finset ι} (x : AnchorChoice C S) :
    weight (fun p : κ × ι => rate p.2) x.requirements = x.cost rate := by
  cases x <;> simp [AnchorChoice.requirements, StaticCertificates.weight, AnchorChoice.cost]

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
lemma AnchorChoice.distinct_events {C : Finset (κ × ι)} {S : Finset ι}
    (x y : AnchorChoice C S) (hne : x.direction ≠ y.direction) :
    Disjoint x.requirements y.requirements := by
  cases x with
  | inl d => exact Finset.disjoint_empty_left _
  | inr rd =>
    cases y with
    | inl d => exact Finset.disjoint_empty_right _
    | inr re =>
      apply Finset.disjoint_singleton_left.mpr
      simp only [AnchorChoice.requirements, Finset.mem_singleton]
      intro he
      exact hne (congrArg Prod.snd he)

omit [Fintype ι] [Fintype κ] in

lemma two_anchor_extension_weight (rate : ι → ℝ≥0)
    {C : Finset (κ × ι)} {S : Finset ι} (x y : AnchorChoice C S)
    (hne : x.direction ≠ y.direction) :
    weight (fun p : κ × ι => rate p.2) (C ∪ (x.requirements ∪ y.requirements)) =
      weight (fun p : κ × ι => rate p.2) C * (x.cost rate * y.cost rate) := by
  rw [weight_union_fresh _ _ _ (Finset.disjoint_union_right.mpr ⟨x.fresh, y.fresh⟩),
    weight_union_fresh _ _ _ (x.distinct_events y hne), x.weight rate, y.weight rate]

omit [Fintype ι] [DecidableEq κ] in
lemma sum_anchor_cost (rate : ι → ℝ≥0) (C : Finset (κ × ι)) (S : Finset ι) :
    (∑ x : AnchorChoice C S, x.cost rate) =
      (S ∩ dictionary C).card + Fintype.card κ * ∑ i ∈ S \ dictionary C, (rate i : ℝ) := by
  rw [Fintype.sum_sum_type]
  simp only [AnchorChoice.cost, Finset.sum_const, Finset.card_univ,
    Fintype.card_coe, nsmul_eq_mul, mul_one, Fintype.sum_prod_type]
  rw [Finset.sum_coe_sort (S \ dictionary C) (fun i => (rate i : ℝ))]

omit [Fintype ι] [DecidableEq κ] in

theorem sum_anchor_cost_le (rate : ι → ℝ≥0) (C : Finset (κ × ι)) (S : Finset ι) :
    (∑ x : AnchorChoice C S, x.cost rate) ≤
      C.card + Fintype.card κ * ∑ i ∈ S, (rate i : ℝ) := by
  rw [sum_anchor_cost]
  apply add_le_add
  · exact_mod_cast (Finset.card_le_card (Finset.inter_subset_right (s₁ := S))).trans
      (dictionary_card_le C)
  · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (by intro i _ _; exact (rate i).coe_nonneg)

section AnchorGeometry
variable {H : Type*} [Fintype H] [DecidableEq H]

omit [DecidableEq H] in
omit [Fintype ι] [DecidableEq κ] in

theorem one_anchor_geometric_cost (rate : ι → ℝ≥0) (C : Finset (κ × ι))
    (S : Finset ι) (lineSet : H → Finset ι) (N₁ : ℕ)
    (hN : ∀ d, (Finset.univ.filter (fun H => d ∈ lineSet H)).card ≤ N₁) :
    (∑ x : AnchorChoice C S, x.cost rate *
      (Finset.univ.filter (fun H => x.direction ∈ lineSet H)).card) ≤
      (N₁ : ℝ) * (C.card + Fintype.card κ * ∑ i ∈ S, (rate i : ℝ)) := by
  calc
    _ ≤ ∑ x : AnchorChoice C S, x.cost rate * N₁ := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (x.cost_nonneg rate)
      exact_mod_cast hN x.direction
    _ = (N₁ : ℝ) * ∑ x : AnchorChoice C S, x.cost rate := by
      rw [← Finset.sum_mul, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_anchor_cost_le rate C S) (Nat.cast_nonneg _)

omit [DecidableEq H] in
omit [Fintype ι] [DecidableEq κ] in

theorem two_anchor_geometric_cost (rate : ι → ℝ≥0) (C : Finset (κ × ι))
    (S : Finset ι) (lineSet : H → Finset ι) (N₂ : ℕ)
    (hN : ∀ d e, d ≠ e →
      (Finset.univ.filter (fun H => d ∈ lineSet H ∧ e ∈ lineSet H)).card ≤ N₂) :
    (∑ x : AnchorChoice C S, ∑ y : AnchorChoice C S,
      if x.direction ≠ y.direction then x.cost rate * y.cost rate *
        (Finset.univ.filter (fun H => x.direction ∈ lineSet H ∧ y.direction ∈ lineSet H)).card
      else 0) ≤
      (N₂ : ℝ) * (C.card + Fintype.card κ * ∑ i ∈ S, (rate i : ℝ)) ^ 2 := by
  classical
  let A : ℝ := ∑ x : AnchorChoice C S, x.cost rate
  have hA : 0 ≤ A := Finset.sum_nonneg (fun x _ => x.cost_nonneg rate)
  calc
    _ ≤ ∑ x : AnchorChoice C S, ∑ y : AnchorChoice C S,
        x.cost rate * y.cost rate * N₂ := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      split_ifs with hxy
      · apply mul_le_mul_of_nonneg_left _ (mul_nonneg (x.cost_nonneg rate) (y.cost_nonneg rate))
        exact_mod_cast hN x.direction y.direction hxy
      · exact mul_nonneg (mul_nonneg (x.cost_nonneg rate) (y.cost_nonneg rate)) (Nat.cast_nonneg _)
    _ = (N₂ : ℝ) * A ^ 2 := by
      simp only [Finset.sum_mul, Finset.mul_sum, A, pow_two]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact pow_le_pow_left₀ hA (sum_anchor_cost_le rate C S) 2

end AnchorGeometry
end PairWitnesses
end SharpRamseyFive.StaticCertificates
end

end OAI
