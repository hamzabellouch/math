import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

namespace OAI

open scoped BigOperators

namespace Balanced.SparsePatterns

noncomputable section
attribute [local instance] Classical.propDecidable

variable {I A : Type*} [Fintype I] [Fintype A]

def differingPositions (base f : I → A) : Finset I :=
  Finset.univ.filter (fun i => f i ≠ base i)

def sparseFunctions (base : I → A) (k : ℕ) : Finset (I → A) :=
  Finset.univ.filter (fun f => (differingPositions base f).card ≤ k)

omit [Fintype A] in
@[simp] theorem mem_differingPositions (base f : I → A) (i : I) :
    i ∈ differingPositions base f ↔ f i ≠ base i := by
  simp [differingPositions]

@[simp] theorem mem_sparseFunctions (base f : I → A) (k : ℕ) :
    f ∈ sparseFunctions base k ↔ (differingPositions base f).card ≤ k := by
  simp [sparseFunctions]

omit [Fintype A] in
@[simp] theorem differingPositions_eq_empty (base f : I → A) :
    differingPositions base f = ∅ ↔ f = base := by
  simp [differingPositions, Finset.filter_eq_empty_iff, funext_iff]

@[simp] theorem sparseFunctions_zero (base : I → A) :
    sparseFunctions base 0 = {base} := by
  ext f
  simp only [mem_sparseFunctions, Nat.le_zero, Finset.card_eq_zero,
    differingPositions_eq_empty, Finset.mem_singleton]

omit [Fintype A] in

theorem differingPositions_update_base (base f : I → A) (i : I) :
    differingPositions base (Function.update f i (base i)) =
      (differingPositions base f).erase i := by
  ext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]

theorem sparseFunctions_succ_subset (base : I → A) (k : ℕ) :
    sparseFunctions base (k + 1) ⊆ sparseFunctions base k ∪
      Finset.univ.biUnion (fun ia : I × A =>
        (sparseFunctions base k).image (fun f => Function.update f ia.1 ia.2)) := by
  intro f hf
  by_cases hsmall : (differingPositions base f).card ≤ k
  · exact Finset.mem_union_left _ ((mem_sparseFunctions base f k).mpr hsmall)
  · have hbound := (mem_sparseFunctions base f (k + 1)).mp hf
    have hpos : 0 < (differingPositions base f).card := by omega
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
    let g := Function.update f i (base i)
    have hg : g ∈ sparseFunctions base k := by
      apply (mem_sparseFunctions base g k).mpr
      rw [show g = Function.update f i (base i) from rfl,
        differingPositions_update_base, Finset.card_erase_of_mem hi]
      omega
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨(i, f i), Finset.mem_univ _, Finset.mem_image.mpr ⟨g, hg, ?_⟩⟩
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [g, Function.update_of_ne hji]

theorem card_sparseFunctions_succ_le (base : I → A) (k : ℕ) :
    (sparseFunctions base (k + 1)).card ≤
      (1 + Fintype.card I * Fintype.card A) * (sparseFunctions base k).card := by
  calc
    (sparseFunctions base (k + 1)).card ≤
        (sparseFunctions base k ∪ Finset.univ.biUnion (fun ia : I × A =>
          (sparseFunctions base k).image (fun f => Function.update f ia.1 ia.2))).card :=
      Finset.card_le_card (sparseFunctions_succ_subset base k)
    _ ≤ (sparseFunctions base k).card +
        (Finset.univ.biUnion (fun ia : I × A =>
          (sparseFunctions base k).image (fun f => Function.update f ia.1 ia.2))).card :=
      Finset.card_union_le _ _
    _ ≤ (sparseFunctions base k).card +
        ∑ ia : I × A, ((sparseFunctions base k).image
          (fun f => Function.update f ia.1 ia.2)).card := by
      exact Nat.add_le_add_left Finset.card_biUnion_le _
    _ ≤ (sparseFunctions base k).card +
        ∑ _ia : I × A, (sparseFunctions base k).card := by
      apply Nat.add_le_add_left
      exact Finset.sum_le_sum fun ia _ => Finset.card_image_le
    _ = (1 + Fintype.card I * Fintype.card A) * (sparseFunctions base k).card := by
      simp [Fintype.card_prod]
      ring

theorem card_sparseFunctions_le (base : I → A) (k : ℕ) :
    (sparseFunctions base k).card ≤ (1 + Fintype.card I * Fintype.card A) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      (sparseFunctions base (k + 1)).card ≤
          (1 + Fintype.card I * Fintype.card A) * (sparseFunctions base k).card :=
        card_sparseFunctions_succ_le base k
      _ ≤ (1 + Fintype.card I * Fintype.card A) *
          (1 + Fintype.card I * Fintype.card A) ^ k := Nat.mul_le_mul_left _ ih
      _ = (1 + Fintype.card I * Fintype.card A) ^ (k + 1) := by rw [pow_succ'];

theorem card_sparse_endomaps_le (N κ : ℕ) :
    (sparseFunctions (id : Fin N → Fin N) κ).card ≤ (1 + N ^ 2) ^ κ := by
  simpa [pow_two] using card_sparseFunctions_le (id : Fin N → Fin N) κ

theorem card_sparse_tuple_maps_le (b κ : ℕ) (hb : 1 ≤ b) (hκ : κ ≤ 2) :
    (sparseFunctions (id : Fin (4 * b) → Fin (4 * b)) κ).card ≤ 289 * b ^ 4 := by
  calc
    (sparseFunctions (id : Fin (4 * b) → Fin (4 * b)) κ).card ≤
        (1 + (4 * b) ^ 2) ^ κ := card_sparse_endomaps_le _ _
    _ ≤ (1 + (4 * b) ^ 2) ^ 2 := pow_le_pow_right₀ (by omega) hκ
    _ ≤ (17 * b ^ 2) ^ 2 := by
      gcongr
      nlinarith
    _ = 289 * b ^ 4 := by ring

section Representatives

variable {J G : Type*} [Fintype J] [LinearOrder J]

def firstOccurrence (f : J → G) (i : J) : J :=
  (Finset.univ.filter (fun j => f j = f i)).min' ⟨i, by simp⟩

theorem value_firstOccurrence (f : J → G) (i : J) :
    f (firstOccurrence f i) = f i := by
  exact (Finset.mem_filter.mp (Finset.min'_mem
    (Finset.univ.filter (fun j => f j = f i)) ⟨i, by simp⟩)).2

theorem firstOccurrence_le (f : J → G) (i : J) : firstOccurrence f i ≤ i := by
  exact Finset.min'_le _ i (by simp)

theorem firstOccurrence_eq_of_value_eq (f : J → G) {i j : J} (h : f i = f j) :
    firstOccurrence f i = firstOccurrence f j := by
  simp only [firstOccurrence, h]

theorem firstOccurrence_eq_iff (f : J → G) (i j : J) :
    firstOccurrence f i = firstOccurrence f j ↔ f i = f j := by
  constructor
  · intro h
    exact (value_firstOccurrence f i).symm.trans
      ((congrArg f h).trans (value_firstOccurrence f j))
  · exact firstOccurrence_eq_of_value_eq f

@[simp] theorem firstOccurrence_idem (f : J → G) (i : J) :
    firstOccurrence f (firstOccurrence f i) = firstOccurrence f i :=
  firstOccurrence_eq_of_value_eq f (value_firstOccurrence f i)

@[simp] theorem mem_firstOccurrence_range (f : J → G) (i : J) :
    i ∈ Finset.univ.image (firstOccurrence f) ↔ firstOccurrence f i = i := by
  constructor
  · intro h
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp h
    exact firstOccurrence_idem f j
  · intro h
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h⟩

theorem card_firstOccurrence_range (f : J → G) :
    (Finset.univ.image (firstOccurrence f)).card = (Finset.univ.image f).card := by
  have hinj : Set.InjOn f (↑(Finset.univ.image (firstOccurrence f)) : Set J) := by
    intro i hi j hj hij
    have hi' := (mem_firstOccurrence_range f i).mp hi
    have hj' := (mem_firstOccurrence_range f j).mp hj
    calc
      i = firstOccurrence f i := hi'.symm
      _ = firstOccurrence f j := firstOccurrence_eq_of_value_eq f hij
      _ = j := hj'
  have himage : (Finset.univ.image (firstOccurrence f)).image f = Finset.univ.image f := by
    rw [Finset.image_image]
    congr 1
    funext i
    exact value_firstOccurrence f i
  have hcard := Finset.card_image_of_injOn hinj
  rw [himage] at hcard
  exact hcard.symm

theorem card_differing_firstOccurrence (f : J → G) :
    (differingPositions id (firstOccurrence f)).card =
      Fintype.card J - (Finset.univ.image f).card := by
  have hd : differingPositions id (firstOccurrence f) =
      Finset.univ \ Finset.univ.image (firstOccurrence f) := by
    ext i
    simp only [mem_differingPositions, id_eq, Finset.mem_sdiff, Finset.mem_univ,
      true_and, mem_firstOccurrence_range]
  rw [hd, Finset.card_sdiff_of_subset (Finset.subset_univ _), card_firstOccurrence_range]
  simp

theorem firstOccurrence_mem_sparse (f : J → G) (κ : ℕ)
    (hκ : Fintype.card J - (Finset.univ.image f).card ≤ κ) :
    firstOccurrence f ∈ sparseFunctions id κ := by
  rw [mem_sparseFunctions, card_differing_firstOccurrence]
  exact hκ

theorem firstOccurrence_eq_iff_same_pattern {H : Type*} (f : J → G) (g : J → H) :
    firstOccurrence f = firstOccurrence g ↔ ∀ i j, (f i = f j ↔ g i = g j) := by
  constructor
  · intro h i j
    rw [← firstOccurrence_eq_iff f, ← firstOccurrence_eq_iff g, h]
  · intro h
    funext i
    unfold firstOccurrence
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact h j i

theorem card_canonical_patterns_le (s : Finset (J → G)) (κ : ℕ)
    (hreuse : ∀ f ∈ s, Fintype.card J - (Finset.univ.image f).card ≤ κ) :
    (s.image firstOccurrence).card ≤ (1 + (Fintype.card J) ^ 2) ^ κ := by
  have hsub : s.image firstOccurrence ⊆ sparseFunctions (id : J → J) κ := by
    intro r hr
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hr
    exact firstOccurrence_mem_sparse f κ (hreuse f hf)
  calc
    (s.image firstOccurrence).card ≤ (sparseFunctions (id : J → J) κ).card :=
      Finset.card_le_card hsub
    _ ≤ (1 + (Fintype.card J) ^ 2) ^ κ := by
      simpa [pow_two] using card_sparseFunctions_le (id : J → J) κ

theorem card_canonical_tuple_patterns_le (b κ : ℕ)
    (s : Finset (Fin (4 * b) → G)) (hb : 1 ≤ b) (hκ : κ ≤ 2)
    (hreuse : ∀ f ∈ s, 4 * b - (Finset.univ.image f).card ≤ κ) :
    (s.image firstOccurrence).card ≤ 289 * b ^ 4 := by
  have hsub : s.image firstOccurrence ⊆
      sparseFunctions (id : Fin (4 * b) → Fin (4 * b)) κ := by
    intro r hr
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hr
    apply firstOccurrence_mem_sparse
    simpa using hreuse f hf
  exact (Finset.card_le_card hsub).trans (card_sparse_tuple_maps_le b κ hb hκ)

theorem exists_canonical_tuple_representatives (b κ : ℕ)
    (s : Finset (Fin (4 * b) → G)) (hb : 1 ≤ b) (hκ : κ ≤ 2)
    (hreuse : ∀ f ∈ s, 4 * b - (Finset.univ.image f).card ≤ κ) :
    ∃ t : Finset (Fin (4 * b) → G), t ⊆ s ∧ t.card ≤ 289 * b ^ 4 ∧
      Set.InjOn firstOccurrence (↑t : Set (Fin (4 * b) → G)) ∧
      ∀ f ∈ s, ∃ g ∈ t, ∀ i j, (g i = g j ↔ f i = f j) := by
  have hsurj : (↑s : Set (Fin (4 * b) → G)).SurjOn firstOccurrence
      (↑(s.image firstOccurrence) : Set (Fin (4 * b) → Fin (4 * b))) := by
    intro r hr
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hr
    exact ⟨f, hf, rfl⟩
  obtain ⟨t, ht, hinj, himage⟩ :=
    Finset.exists_subset_injOn_image_eq_of_surjOn
      (↑s : Set (Fin (4 * b) → G)) (s.image firstOccurrence) hsurj
  refine ⟨t, ht, ?_, hinj, ?_⟩
  · calc
      t.card = (t.image firstOccurrence).card := (Finset.card_image_of_injOn hinj).symm
      _ = (s.image firstOccurrence).card := congrArg Finset.card himage
      _ ≤ 289 * b ^ 4 := card_canonical_tuple_patterns_le b κ s hb hκ hreuse
  · intro f hf
    have hmem : firstOccurrence f ∈ t.image firstOccurrence := by
      rw [himage]
      exact Finset.mem_image.mpr ⟨f, hf, rfl⟩
    obtain ⟨g, hg, hgf⟩ := Finset.mem_image.mp hmem
    exact ⟨g, hg, (firstOccurrence_eq_iff_same_pattern g f).mp hgf⟩

end Representatives

section Relabeling

variable {X Y Z D : Type*}

theorem exists_relabeling_of_same_pattern (f : X → Y) (g : X → Z)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hpattern : ∀ i j, (f i = f j ↔ g i = g j)) :
    ∃ e : Y ≃ Z, ∀ i, e (f i) = g i := by
  let r : Y → X := fun y => Classical.choose (hf y)
  have hr : ∀ y, f (r y) = y := fun y => Classical.choose_spec (hf y)
  let e : Y → Z := fun y => g (r y)
  have hfactor : ∀ i, e (f i) = g i := fun i =>
    (hpattern (r (f i)) i).mp (hr (f i))
  have hinj : Function.Injective e := by
    intro y z hyz
    have h := (hpattern (r y) (r z)).mpr hyz
    simpa only [hr] using h
  have hsurj : Function.Surjective e := by
    intro z
    obtain ⟨i, rfl⟩ := hg z
    exact ⟨f i, hfactor i⟩
  exact ⟨Equiv.ofBijective e ⟨hinj, hsurj⟩, hfactor⟩

theorem exists_assignment_equiv_of_same_pattern (f : X → Y) (g : X → Z)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hpattern : ∀ i j, (f i = f j ↔ g i = g j)) :
    ∃ e : (Y → D) ≃ (Z → D), ∀ a i, (e a) (g i) = a (f i) := by
  obtain ⟨e, he⟩ := exists_relabeling_of_same_pattern f g hf hg hpattern
  refine ⟨Equiv.arrowCongr e (Equiv.refl D), ?_⟩
  intro a i
  change a (e.symm (g i)) = a (f i)
  rw [← he i, e.symm_apply_apply]

theorem sum_assignments_eq_of_same_pattern [Fintype Y] [Fintype Z] [Fintype D]
    (f : X → Y) (g : X → Z) (hf : Function.Surjective f)
    (hg : Function.Surjective g) (hpattern : ∀ i j, (f i = f j ↔ g i = g j))
    (test : (X → D) → ℝ) :
    (∑ a : Y → D, test (a ∘ f)) = ∑ a : Z → D, test (a ∘ g) := by
  obtain ⟨e, he⟩ := exists_assignment_equiv_of_same_pattern (D := D) f g hf hg hpattern
  apply Fintype.sum_equiv e
  intro a
  congr 1
  funext i
  exact (he a i).symm

end Relabeling

end
end Balanced.SparsePatterns

end OAI
