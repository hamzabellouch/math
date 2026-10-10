import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OAI

namespace RyserCoveringCounterexample.Construction

open scoped BigOperators

variable {G P : Type*}

theorem exists_selection_card_eq
    (I : Finset G) (W : G → Finset P) (n : ℕ)
    (hW : ∀ i ∈ I, n ≤ (W i).card) :
    ∃ S : G → Finset P,
      (∀ i ∈ I, S i ⊆ W i ∧ (S i).card = n) ∧
      (∀ i ∉ I, S i = ∅) := by
  classical
  have hchoose (i : G) (hi : i ∈ I) :
      ∃ T : Finset P, T ⊆ W i ∧ T.card = n :=
    Finset.exists_subset_card_eq (hW i hi)
  let S : G → Finset P := fun i =>
    if hi : i ∈ I then Classical.choose (hchoose i hi) else ∅
  refine ⟨S, ?_, ?_⟩
  · intro i hi
    simpa only [S, dite_eq_left hi] using Classical.choose_spec (hchoose i hi)
  · intro i hi
    simp only [S, dite_eq_right hi]

theorem exists_five_selection
    (I : Finset G) (W : G → Finset P)
    (hW : ∀ i ∈ I, 5 ≤ (W i).card) :
    ∃ S : G → Finset P,
      (∀ i ∈ I, S i ⊆ W i ∧ (S i).card = 5) ∧
      (∀ i ∉ I, S i = ∅) :=
  exists_selection_card_eq I W 5 hW

variable [DecidableEq G] [instDecidableEqP : DecidableEq P]

def selectedPositions (I : Finset G) (S : G → Finset P) : Finset (G × P) :=
  I.biUnion (fun i => (S i).image (fun w => (i, w)))

@[simp] theorem mem_selectedPositions
    {I : Finset G} {S : G → Finset P} {x : G × P} :
    x ∈ selectedPositions I S ↔ x.1 ∈ I ∧ x.2 ∈ S x.1 := by
  rcases x with ⟨i, w⟩
  simp [selectedPositions]

theorem card_selectedPositions_eq_sum (I : Finset G) (S : G → Finset P) :
    (selectedPositions I S).card = ∑ i ∈ I, (S i).card := by
  have hdisjoint : (I : Set G).PairwiseDisjoint
      (fun i => (S i).image (fun w => (i, w))) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨w, _, hx⟩ := Finset.mem_image.mp hx
    obtain ⟨z, _, hy⟩ := Finset.mem_image.mp hy
    exact hij ((congrArg Prod.fst hx).trans (congrArg Prod.fst hy).symm)
  calc
    (selectedPositions I S).card =
        ∑ i ∈ I, ((S i).image (fun w => (i, w))).card :=
      Finset.card_biUnion hdisjoint
    _ = ∑ i ∈ I, (S i).card := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.card_image_of_injective _
        (fun w z hwz => congrArg Prod.snd hwz)

theorem card_selectedPositions (I : Finset G) (S : G → Finset P) (n : ℕ)
    (hS : ∀ i ∈ I, (S i).card = n) :
    (selectedPositions I S).card = n * I.card := by
  calc
    (selectedPositions I S).card = ∑ i ∈ I, (S i).card :=
      card_selectedPositions_eq_sum I S
    _ = I.card * n := Finset.sum_const_nat hS
    _ = n * I.card := Nat.mul_comm _ _

theorem card_eq_card_image_fst_of_one_per_group
    (E : Finset (G × P))
    (hE : ∀ (i : G) (w z : P), (i, w) ∈ E → (i, z) ∈ E → w = z) :
    E.card = (E.image Prod.fst).card := let _ := instDecidableEqP; by
  symm
  apply Finset.card_image_of_injOn
  intro x hx y hy hxy
  rcases x with ⟨i, w⟩
  rcases y with ⟨j, z⟩
  change i = j at hxy
  subst j
  exact congrArg (fun p : P => (i, p)) (hE i w z hx hy)

theorem card_le_card_image_fst_of_one_per_group
    (E : Finset (G × P))
    (hE : ∀ (i : G) (w z : P), (i, w) ∈ E → (i, z) ∈ E → w = z) :
    E.card ≤ (E.image Prod.fst).card :=
  (card_eq_card_image_fst_of_one_per_group E hE).le

theorem card_le_selected_group_of_subset
    (I : Finset G) (S : G → Finset P) (E : Finset (G × P)) (i : G)
    (hE : E ⊆ selectedPositions I S)
    (hgroup : ∀ x ∈ E, x.1 = i) :
    E.card ≤ (S i).card := by
  apply Finset.card_le_card_of_injOn Prod.snd
  · intro x hx
    change x.2 ∈ S i
    have hs : x.2 ∈ S x.1 := (mem_selectedPositions.mp (hE hx)).2
    rw [hgroup x hx] at hs
    exact hs
  · intro x hx y hy hxy
    exact Prod.ext ((hgroup x hx).trans (hgroup y hy).symm) hxy

theorem card_le_five_of_subset_selectedPositions_one_group
    (I : Finset G) (S : G → Finset P) (E : Finset (G × P)) (i : G)
    (hE : E ⊆ selectedPositions I S)
    (hgroup : ∀ x ∈ E, x.1 = i)
    (hS : (S i).card ≤ 5) :
    E.card ≤ 5 :=
  (card_le_selected_group_of_subset I S E i hE hgroup).trans hS

end RyserCoveringCounterexample.Construction

end OAI
