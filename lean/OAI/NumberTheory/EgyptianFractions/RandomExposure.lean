import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.RandomExposure

/-- Two disjoint equally sized groups can be selected from a sufficiently large finite set. -/
theorem exists_two_disjoint_subsets {α : Type*} [DecidableEq α]
    (D : Finset α) (s : ℕ) (hsize : 2 * s ≤ D.card) :
    ∃ A B : Finset α, A ⊆ D ∧ B ⊆ D ∧ Disjoint A B ∧ A.card = s ∧ B.card = s := by
  obtain ⟨A, hAD, hA⟩ := Finset.exists_subset_card_eq (show s ≤ D.card by omega)
  have hremain : s ≤ (D \ A).card := by
    rw [Finset.card_sdiff_of_subset hAD, hA]
    omega
  obtain ⟨B, hB, hBs⟩ := Finset.exists_subset_card_eq hremain
  refine ⟨A, B, hAD, hB.trans Finset.sdiff_subset, ?_, hA, hBs⟩
  apply Finset.disjoint_left.mpr
  intro i hiA hiB
  exact (Finset.mem_sdiff.mp (hB hiB)).2 hiA

/-- Select the two fresh groups for a pair of Boolean words with enough differing positions. -/
theorem exists_differing_blocks {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I J : ι → Bool) (s : ℕ)
    (hsize : 2 * s ≤ (Finset.univ.filter fun i => I i ≠ J i).card) :
    ∃ A B : Finset ι, Disjoint A B ∧ A.card = s ∧ B.card = s ∧
      (∀ i ∈ A, I i ≠ J i) ∧ (∀ i ∈ B, I i ≠ J i) := by
  obtain ⟨A, B, hA, hB, hAB, hAs, hBs⟩ :=
    exists_two_disjoint_subsets (Finset.univ.filter fun i => I i ≠ J i) s hsize
  refine ⟨A, B, hAB, hAs, hBs, ?_, ?_⟩
  · intro i hi
    exact (Finset.mem_filter.mp (hA hi)).2
  · intro i hi
    exact (Finset.mem_filter.mp (hB hi)).2

/-- Reindex all labelled samples into two free blocks and their exposed complement. -/
def splitSample {α β : Type*} [DecidableEq α] (A B : Finset α) (hAB : Disjoint A B) :
    (α → β) ≃ ((A → β) × (B → β) × ({i : α // i ∉ A ∧ i ∉ B} → β)) where
  toFun f := (fun i => f i, fun i => f i, fun i => f i)
  invFun f i := if ha : i ∈ A then f.1 ⟨i, ha⟩ else
    if hb : i ∈ B then f.2.1 ⟨i, hb⟩ else f.2.2 ⟨i, ha, hb⟩
  left_inv f := by
    funext i
    dsimp
    split_ifs <;> rfl
  right_inv f := by
    rcases f with ⟨a, b, c⟩
    apply Prod.ext
    · funext i
      simp [i.property]
    apply Prod.ext
    · funext i
      have hiA : (i : α) ∉ A := fun h => (Finset.disjoint_left.mp hAB) h i.property
      simp [hiA, i.property]
    · funext i
      simp [i.property.1, i.property.2]

@[simp] theorem splitSample_symm_left {α β : Type*} [DecidableEq α]
    (A B : Finset α) (hAB : Disjoint A B)
    (a : A → β) (b : B → β) (c : {i : α // i ∉ A ∧ i ∉ B} → β) (i : A) :
    (splitSample A B hAB).symm (a, b, c) i = a i := by
  simp [splitSample, i.property]

@[simp] theorem splitSample_symm_right {α β : Type*} [DecidableEq α]
    (A B : Finset α) (hAB : Disjoint A B)
    (a : A → β) (b : B → β) (c : {i : α // i ∉ A ∧ i ∉ B} → β) (i : B) :
    (splitSample A B hAB).symm (a, b, c) i = b i := by
  have hiA : (i : α) ∉ A := fun h => Finset.disjoint_left.mp hAB h i.property
  simp [splitSample, hiA, i.property]

@[simp] theorem splitSample_symm_exposed {α β : Type*} [DecidableEq α]
    (A B : Finset α) (hAB : Disjoint A B)
    (a : A → β) (b : B → β) (c : {i : α // i ∉ A ∧ i ∉ B} → β)
    (i : {i : α // i ∉ A ∧ i ∉ B}) :
    (splitSample A B hAB).symm (a, b, c) i = c i := by
  simp [splitSample, i.property.1, i.property.2]

/-- The same exposure equivalence with exposed samples first, ready for conditional averages. -/
def splitSampleExposedFirst {α β : Type*} [DecidableEq α]
    (A B : Finset α) (hAB : Disjoint A B) :
    (α → β) ≃ (({i : α // i ∉ A ∧ i ∉ B} → β) × ((A → β) × (B → β))) :=
  (splitSample A B hAB).trans
    ((Equiv.prodAssoc _ _ _).symm.trans (Equiv.prodComm _ _))

@[simp] theorem splitSampleExposedFirst_symm {α β : Type*} [DecidableEq α]
    (A B : Finset α) (hAB : Disjoint A B)
    (a : A → β) (b : B → β) (c : {i : α // i ∉ A ∧ i ∉ B} → β) :
    (splitSampleExposedFirst A B hAB).symm (c, a, b) =
      (splitSample A B hAB).symm (a, b, c) := rfl

/-- Fubini's identity for the finite exposure partition; no independence assumption is hidden. -/
theorem sum_splitSample {α β M : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [AddCommMonoid M] (A B : Finset α) (hAB : Disjoint A B) (F : (α → β) → M) :
    (∑ p, F p) = ∑ a : A → β, ∑ b : B → β,
      ∑ c : {i : α // i ∉ A ∧ i ∉ B} → β,
        F ((splitSample A B hAB).symm (a, b, c)) := by
  classical
  have h := (splitSample (β := β) A B hAB).symm.sum_comp F
  simpa only [Fintype.sum_prod_type] using h.symm

/-- The labelled coordinates selected by a Boolean word on a given coordinate set. -/
def selectedLabels {ι : Type*} [DecidableEq ι] (I : ι → Bool) (A : Finset ι) :
    Finset (ι × Bool) := A.image (fun i => (i, I i))

@[simp] theorem mem_selectedLabels {ι : Type*} [DecidableEq ι]
    (I : ι → Bool) (A : Finset ι) (i : ι) (b : Bool) :
    (i, b) ∈ selectedLabels I A ↔ i ∈ A ∧ b = I i := by
  simp [selectedLabels, Prod.mk.injEq, and_left_comm, eq_comm]

@[simp] theorem selectedLabels_card {ι : Type*} [DecidableEq ι]
    (I : ι → Bool) (A : Finset ι) : (selectedLabels I A).card = A.card := by
  apply Finset.card_image_of_injective
  intro i j h
  exact congrArg Prod.fst h

theorem selectedLabels_disjoint {ι : Type*} [DecidableEq ι]
    (I : ι → Bool) {A B : Finset ι} (hAB : Disjoint A B) :
    Disjoint (selectedLabels I A) (selectedLabels I B) := by
  apply Finset.disjoint_left.mpr
  rintro ⟨i, b⟩ hiA hiB
  exact Finset.disjoint_left.mp hAB (mem_selectedLabels I A i b |>.mp hiA).1
    (mem_selectedLabels I B i b |>.mp hiB).1

theorem product_selectedLabels {ι M : Type*} [DecidableEq ι] [CommMonoid M]
    (I : ι → Bool) (A : Finset ι) (p : ι × Bool → M) :
    (∏ i ∈ A, p (i, I i)) = ∏ z : selectedLabels I A, p z := by
  rw [Finset.prod_coe_sort]
  symm
  apply Finset.prod_image
  intro i _ j _ h
  exact congrArg Prod.fst h

/-- Factor the first word's product into exposed and two free coordinate groups. -/
theorem selected_product_factorization {ι M : Type*} [Fintype ι] [DecidableEq ι]
    [CommMonoid M] (I : ι → Bool) (A B : Finset ι) (hAB : Disjoint A B)
    (p : ι × Bool → M) :
    (∏ i, p (i, I i)) =
      (∏ i ∈ Finset.univ \ (A ∪ B), p (i, I i)) *
      (∏ i ∈ A, p (i, I i)) * (∏ i ∈ B, p (i, I i)) := by
  have h := Finset.prod_sdiff (f := fun i => p (i, I i)) (Finset.subset_univ (A ∪ B))
  rw [Finset.prod_union hAB] at h
  simpa only [mul_assoc] using h.symm

/-- The other word uses none of the free labelled samples when the coordinates differ. -/
theorem other_word_exposed {ι : Type*} [DecidableEq ι]
    (I J : ι → Bool) (A : Finset ι) (hdiff : ∀ i ∈ A, I i ≠ J i) (i : ι) :
    (i, J i) ∉ selectedLabels I A := by
  rw [mem_selectedLabels]
  rintro ⟨hi, heq⟩
  exact hdiff i hi heq.symm

/-- Products selected by the other word are unchanged by varying only free samples. -/
theorem other_product_invariant {ι M : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid M]
    (I J : ι → Bool) (A B : Finset ι)
    (hA : ∀ i ∈ A, I i ≠ J i) (hB : ∀ i ∈ B, I i ≠ J i)
    (p q : ι × Bool → M)
    (hpq : ∀ z, z ∉ selectedLabels I A → z ∉ selectedLabels I B → p z = q z) :
    (∏ i, p (i, J i)) = ∏ i, q (i, J i) := by
  apply Finset.prod_congr rfl
  intro i _
  exact hpq (i, J i) (other_word_exposed I J A hA i) (other_word_exposed I J B hB i)

/-- The exposed label set. -/
abbrev ExposedLabel {ι : Type*} [DecidableEq ι]
    (I : ι → Bool) (A B : Finset ι) :=
  {z : ι × Bool // z ∉ selectedLabels I A ∧ z ∉ selectedLabels I B}

/-- Every remaining coordinate of the first word is an exposed labelled sample. -/
def outsideSelectedLabel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I : ι → Bool) (A B : Finset ι) (i : ↥(Finset.univ \ (A ∪ B))) : ExposedLabel I A B := by
  have hiAB : (i : ι) ∉ A ∪ B := (Finset.mem_sdiff.mp i.property).2
  have hi : (i : ι) ∉ A ∧ (i : ι) ∉ B := by
    exact ⟨fun h => hiAB (Finset.mem_union_left B h), fun h => hiAB (Finset.mem_union_right A h)⟩
  exact ⟨(i, I i), by simpa using hi.1, by simpa using hi.2⟩

theorem outsideSelectedLabel_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I : ι → Bool) (A B : Finset ι) : Function.Injective (outsideSelectedLabel I A B) := by
  intro i j h
  apply Subtype.ext
  exact congrArg (fun z : ExposedLabel I A B => z.val.1) h

theorem outside_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Finset ι) (hAB : Disjoint A B) :
    (Finset.univ \ (A ∪ B)).card = Fintype.card ι - (A.card + B.card) := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_union_of_disjoint hAB, Finset.card_univ]

/-- The first word's exposed factor, with an explicit product over the non-fresh coordinates. -/
def exposedFirstProduct {ι β M : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid M]
    (v : β → M) (I : ι → Bool) (A B : Finset ι) (c : ExposedLabel I A B → β) : M :=
  ∏ i : ↥(Finset.univ \ (A ∪ B)), v (c (outsideSelectedLabel I A B i))

/-- All coordinates of the second word remain exposed. -/
def exposedOtherProduct {ι β M : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid M]
    (v : β → M) (I J : ι → Bool) (A B : Finset ι)
    (hA : ∀ i ∈ A, I i ≠ J i) (hB : ∀ i ∈ B, I i ≠ J i)
    (c : ExposedLabel I A B → β) : M :=
  ∏ i, v (c ⟨(i, J i), other_word_exposed I J A hA i, other_word_exposed I J B hB i⟩)

/-- Explicit form of the exposed factor, useful for bounding the bad gcd event. -/
theorem exposed_first_factor_formula {ι β M : Type*} [Fintype ι] [DecidableEq ι]
    [CommMonoid M] (v : β → M) (I : ι → Bool) (A B : Finset ι) (hAB : Disjoint A B)
    (a : selectedLabels I A → β) (b : selectedLabels I B → β) (c : ExposedLabel I A B → β) :
    (∏ i ∈ Finset.univ \ (A ∪ B),
      v ((splitSample _ _ (selectedLabels_disjoint I hAB)).symm (a, b, c) (i, I i))) =
      exposedFirstProduct v I A B c := by
  rw [← Finset.prod_coe_sort]
  unfold exposedFirstProduct
  apply Finset.prod_congr rfl
  intro i _
  exact congrArg v (splitSample_symm_exposed _ _ _ a b c (outsideSelectedLabel I A B i))

theorem exposed_other_factor_formula {ι β M : Type*} [Fintype ι] [DecidableEq ι]
    [CommMonoid M] (v : β → M) (I J : ι → Bool) (A B : Finset ι) (hAB : Disjoint A B)
    (hA : ∀ i ∈ A, I i ≠ J i) (hB : ∀ i ∈ B, I i ≠ J i)
    (a : selectedLabels I A → β) (b : selectedLabels I B → β) (c : ExposedLabel I A B → β) :
    (∏ i, v ((splitSample _ _ (selectedLabels_disjoint I hAB)).symm (a, b, c) (i, J i))) =
      exposedOtherProduct v I J A B hA hB c := by
  apply Finset.prod_congr rfl
  intro i _
  exact congrArg v (splitSample_symm_exposed _ _ _ a b c
    ⟨(i, J i), other_word_exposed I J A hA i, other_word_exposed I J B hB i⟩)

/-- The exact exposed-variable factorization used in the random-product correlation argument.
The two free blocks affect only the first word, each through its own product. -/
theorem exposed_product_factorization {ι β M : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty β] [CommMonoid M] (v : β → M)
    (I J : ι → Bool) (A B : Finset ι) (hAB : Disjoint A B)
    (hA : ∀ i ∈ A, I i ≠ J i) (hB : ∀ i ∈ B, I i ≠ J i) :
    let E := splitSample (β := β) (selectedLabels I A) (selectedLabels I B)
      (selectedLabels_disjoint I hAB)
    ∃ U V : ({z : ι × Bool // z ∉ selectedLabels I A ∧ z ∉ selectedLabels I B} → β) → M,
      ∀ a b c,
        (∏ i, v (E.symm (a, b, c) (i, I i))) =
          U c * (∏ z, v (a z)) * (∏ z, v (b z)) ∧
        (∏ i, v (E.symm (a, b, c) (i, J i))) = V c := by
  classical
  dsimp only
  let E := splitSample (β := β) (selectedLabels I A) (selectedLabels I B)
    (selectedLabels_disjoint I hAB)
  let d : β := Classical.choice inferInstance
  let p0 := fun c => E.symm ((fun _ => d), (fun _ => d), c)
  refine ⟨fun c => ∏ i ∈ Finset.univ \ (A ∪ B), v (p0 c (i, I i)),
    fun c => ∏ i, v (p0 c (i, J i)), ?_⟩
  intro a b c
  let p := E.symm (a, b, c)
  have heq : ∀ z, z ∉ selectedLabels I A → z ∉ selectedLabels I B →
      v (p z) = v (p0 c z) := by
    intro z hzA hzB
    simp [p, p0, E, splitSample, hzA, hzB]
  constructor
  · change (∏ i, (fun z => v (p z)) (i, I i)) = _
    rw [selected_product_factorization I A B hAB (fun z => v (p z))]
    have hexp : (∏ i ∈ Finset.univ \ (A ∪ B), v (p (i, I i))) =
        ∏ i ∈ Finset.univ \ (A ∪ B), v (p0 c (i, I i)) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hi' : i ∉ A ∧ i ∉ B := by simpa using hi
      apply heq
      · simpa using hi'.1
      · simpa using hi'.2
    have hfreeA : (∏ i ∈ A, v (p (i, I i))) = ∏ z, v (a z) := by
      rw [product_selectedLabels I A (fun z => v (p z))]
      apply Finset.prod_congr rfl
      intro z _
      exact congrArg v (splitSample_symm_left _ _ _ a b c z)
    have hfreeB : (∏ i ∈ B, v (p (i, I i))) = ∏ z, v (b z) := by
      rw [product_selectedLabels I B (fun z => v (p z))]
      apply Finset.prod_congr rfl
      intro z _
      exact congrArg v (splitSample_symm_right _ _ _ a b c z)
    change (∏ i ∈ Finset.univ \ (A ∪ B), v (p (i, I i))) *
      (∏ i ∈ A, v (p (i, I i))) * (∏ i ∈ B, v (p (i, I i))) = _
    rw [hexp, hfreeA, hfreeB]
  · exact other_product_invariant I J A B hA hB (fun z => v (p z))
      (fun z => v (p0 c z)) heq

end Problem337.RandomExposure

end

end OAI
