import Mathlib

namespace OAI

/-!
The finite-map counting lemma in `collisions.tex`, Lemma `finite-map`.
The collision count records ordered distinct pairs of good tuples with the
same image.  Both the exceptional values and all tuples above them are bounded.
-/

open scoped BigOperators

namespace TotientAsymptotic.FiniteMap

variable {α β : Type*} [DecidableEq β]

def fiber (G : Finset α) (F : α → β) (w : β) : Finset α :=
  G.filter (fun t => F t = w)

def collisionCount (G : Finset α) (W : Finset β) (F : α → β) : ℕ :=
  ∑ w ∈ W, (fiber G F w).card * ((fiber G F w).card - 1)

def multipleValues (G : Finset α) (W : Finset β) (F : α → β) : Finset β :=
  W.filter (fun w => 2 ≤ (fiber G F w).card)

def badValues (G D : Finset α) (W E : Finset β) (F : α → β) : Finset β :=
  E ∪ D.image F ∪ multipleValues G W F

def badPreimages (T G D : Finset α) (W E : Finset β) (F : α → β) : Finset α :=
  T.filter (fun t => F t ∈ badValues G D W E F)

lemma collisionCount_eq_ordered_pairs [DecidableEq α]
    (G : Finset α) (W : Finset β) (F : α → β)
    (hmap : ∀ t ∈ G, F t ∈ W) :
    collisionCount G W F = (G.offDiag.filter (fun p => F p.1 = F p.2)).card := by
  have hdisjoint : (W : Set β).PairwiseDisjoint (fun w => (fiber G F w).offDiag) := by
    intro u _ v _ huv
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hp' := (Finset.mem_filter.mp (Finset.mem_offDiag.mp hp).1).2
    have hq' := (Finset.mem_filter.mp (Finset.mem_offDiag.mp hq).1).2
    exact huv (hp'.symm.trans hq')
  have hunion : W.biUnion (fun w => (fiber G F w).offDiag) =
      G.offDiag.filter (fun p => F p.1 = F p.2) := by
    ext p
    constructor
    · intro hp
      obtain ⟨w, _, hp⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨ha, hb, hne⟩ := Finset.mem_offDiag.mp hp
      obtain ⟨ha, hfa⟩ := Finset.mem_filter.mp ha
      obtain ⟨hb, hfb⟩ := Finset.mem_filter.mp hb
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_offDiag.mpr ⟨ha, hb, hne⟩, hfa.trans hfb.symm⟩
    · intro hp
      obtain ⟨hp, heq⟩ := Finset.mem_filter.mp hp
      obtain ⟨ha, hb, hne⟩ := Finset.mem_offDiag.mp hp
      apply Finset.mem_biUnion.mpr
      refine ⟨F p.1, hmap _ ha, Finset.mem_offDiag.mpr ⟨?_, ?_, hne⟩⟩
      · exact Finset.mem_filter.mpr ⟨ha, rfl⟩
      · exact Finset.mem_filter.mpr ⟨hb, heq.symm⟩
  rw [← hunion, Finset.card_biUnion hdisjoint]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.offDiag_card, Nat.mul_sub_one]

private lemma twice_le_two_add_pairs (r : ℕ) : 2*r ≤ 2 + r*(r-1) := by
  cases r with
  | zero => norm_num
  | succ n =>
    cases n with
    | zero => norm_num
    | succ n => simp only [Nat.add_sub_cancel]; nlinarith

private lemma two_le_pairs {r : ℕ} (hr : 2 ≤ r) : 2 ≤ r*(r-1) := by
  have hsub : 1 ≤ r-1 := by omega
  nlinarith

lemma good_preimage_bound (G : Finset α) (W B : Finset β) (F : α → β)
    (hB : B ⊆ W) :
    2 * (G.filter (fun t => F t ∈ B)).card ≤ 2*B.card + collisionCount G W F := by
  have hsum : ∑ w ∈ B, (fiber G F w).card * ((fiber G F w).card - 1) ≤
      collisionCount G W F :=
    Finset.sum_le_sum_of_subset_of_nonneg hB (fun _ _ _ => Nat.zero_le _)
  calc
    2 * (G.filter (fun t => F t ∈ B)).card = ∑ w ∈ B, 2*(fiber G F w).card := by
      rw [← Finset.sum_card_fiberwise_eq_card_filter G B F, Finset.mul_sum]
      rfl
    _ ≤ ∑ w ∈ B, (2 + (fiber G F w).card * ((fiber G F w).card - 1)) :=
      Finset.sum_le_sum (fun _ _ => twice_le_two_add_pairs _)
    _ = 2*B.card + ∑ w ∈ B, (fiber G F w).card * ((fiber G F w).card - 1) := by
      simp [Finset.sum_add_distrib, Nat.mul_comm]
    _ ≤ 2*B.card + collisionCount G W F := Nat.add_le_add_left hsum _

lemma multiple_values_bound (G : Finset α) (W : Finset β) (F : α → β) :
    2*(multipleValues G W F).card ≤ collisionCount G W F := by
  calc
    2*(multipleValues G W F).card = ∑ _w ∈ multipleValues G W F, 2 := by
      simp [Nat.mul_comm]
    _ ≤ ∑ w ∈ multipleValues G W F,
        (fiber G F w).card * ((fiber G F w).card - 1) := by
      apply Finset.sum_le_sum
      intro w hw
      exact two_le_pairs (Finset.mem_filter.mp hw).2
    _ ≤ collisionCount G W F :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => Nat.zero_le _)

lemma bad_values_subset (G D : Finset α) (W E : Finset β) (F : α → β)
    (hE : E ⊆ W) (hD : ∀ t ∈ D, F t ∈ W) : badValues G D W E F ⊆ W := by
  intro w hw
  rcases Finset.mem_union.mp hw with hw | hw
  · rcases Finset.mem_union.mp hw with hw | hw
    · exact hE hw
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hw
      exact hD t ht
  · exact (Finset.mem_filter.mp hw).1

lemma bad_values_bound (G D : Finset α) (W E : Finset β) (F : α → β) :
    2*(badValues G D W E F).card ≤
      2*E.card + 2*D.card + collisionCount G W F := by
  have h₁ := Finset.card_union_le (E ∪ D.image F) (multipleValues G W F)
  have h₂ := Finset.card_union_le E (D.image F)
  have h₃ := Finset.card_image_le (s := D) (f := F)
  have h₄ := multiple_values_bound G W F
  change 2*((E ∪ D.image F) ∪ multipleValues G W F).card ≤ _
  omega

/-- The manuscript's finite-map lemma, with all half-collision bounds expressed
over the reals and the bijection expressed as `Set.BijOn`. -/
theorem counting [DecidableEq α] (T G D : Finset α) (W E : Finset β) (F : α → β)
    (hpartition : T = G ∪ D) (hdisjoint : Disjoint G D)
    (hmap : ∀ t ∈ T, F t ∈ W) (hE : E ⊆ W)
    (hcoverage : W \ E ⊆ T.image F) :
    (-(E.card : ℝ) ≤ (T.card : ℝ) - W.card) ∧
    ((T.card : ℝ) - W.card ≤ D.card + (collisionCount G W F : ℝ)/2) ∧
    ((badValues G D W E F).card : ℝ) ≤
      E.card + D.card + (collisionCount G W F : ℝ)/2 ∧
    ((badPreimages T G D W E F).card : ℝ) ≤
      E.card + 2*D.card + collisionCount G W F ∧
    Set.BijOn F (↑(T \ badPreimages T G D W E F))
      (↑(W \ badValues G D W E F)) := by
  have hGT : G ⊆ T := by rw [hpartition]; exact Finset.subset_union_left
  have hDT : D ⊆ T := by rw [hpartition]; exact Finset.subset_union_right
  have hGmap : ∀ t ∈ G, F t ∈ W := fun t ht => hmap t (hGT ht)
  have hDmap : ∀ t ∈ D, F t ∈ W := fun t ht => hmap t (hDT ht)
  have hbadsub := bad_values_subset G D W E F hE hDmap
  have hcardT : T.card = G.card + D.card := by
    rw [hpartition, Finset.card_union_of_disjoint hdisjoint]
  have hgood : 2*G.card ≤ 2*W.card + collisionCount G W F := by
    have h := good_preimage_bound G W W F (fun _ hw => hw)
    have hfilter : G.filter (fun t => F t ∈ W) = G :=
      Finset.filter_eq_self.mpr hGmap
    rwa [hfilter] at h
  have hlower : W.card ≤ T.card + E.card := by
    have h₁ := Finset.card_le_card hcoverage
    have h₂ := Finset.card_image_le (s := T) (f := F)
    have h₃ := Finset.card_sdiff_add_card_eq_card hE
    omega
  have hbad := bad_values_bound G D W E F
  have hpre : (badPreimages T G D W E F).card ≤
      E.card + 2*D.card + collisionCount G W F := by
    have hgpre := good_preimage_bound G W (badValues G D W E F) F hbadsub
    have hsplit : badPreimages T G D W E F =
        G.filter (fun t => F t ∈ badValues G D W E F) ∪
          D.filter (fun t => F t ∈ badValues G D W E F) := by
      simp only [badPreimages, hpartition, Finset.filter_union]
    have h₁ := Finset.card_union_le
      (G.filter (fun t => F t ∈ badValues G D W E F))
      (D.filter (fun t => F t ∈ badValues G D W E F))
    have h₂ := Finset.card_filter_le D (fun t => F t ∈ badValues G D W E F)
    rw [hsplit]
    omega
  have hbij : Set.BijOn F (↑(T \ badPreimages T G D W E F))
      (↑(W \ badValues G D W E F)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro t ht
      obtain ⟨ht, hnot⟩ := Finset.mem_sdiff.mp ht
      exact Finset.mem_sdiff.mpr ⟨hmap t ht, fun h =>
        hnot (Finset.mem_filter.mpr ⟨ht, h⟩)⟩
    · intro a ha b hb hab
      obtain ⟨ha, haout⟩ := Finset.mem_sdiff.mp ha
      obtain ⟨hb, hbout⟩ := Finset.mem_sdiff.mp hb
      have haout' : F a ∉ badValues G D W E F := fun h =>
        haout (Finset.mem_filter.mpr ⟨ha, h⟩)
      have hbout' : F b ∉ badValues G D W E F := fun h =>
        hbout (Finset.mem_filter.mpr ⟨hb, h⟩)
      have hag : a ∈ G := by
        rw [hpartition] at ha
        rcases Finset.mem_union.mp ha with h | h
        · exact h
        · exact False.elim (haout' (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a, h, rfl⟩))))
      have hbg : b ∈ G := by
        rw [hpartition] at hb
        rcases Finset.mem_union.mp hb with h | h
        · exact h
        · exact False.elim (hbout' (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b, h, rfl⟩))))
      have hr : (fiber G F (F a)).card ≤ 1 := by
        by_contra h
        have hm : F a ∈ multipleValues G W F :=
          Finset.mem_filter.mpr ⟨hmap a (hGT hag), by omega⟩
        exact haout' (Finset.mem_union_right _ hm)
      exact Finset.card_le_one.mp hr a (Finset.mem_filter.mpr ⟨hag, rfl⟩)
        b (Finset.mem_filter.mpr ⟨hbg, hab.symm⟩)
    · intro w hw
      obtain ⟨hw, hwout⟩ := Finset.mem_sdiff.mp hw
      have hwe : w ∉ E := fun h => hwout
        (Finset.mem_union_left _ (Finset.mem_union_left _ h))
      obtain ⟨t, ht, htw⟩ := Finset.mem_image.mp
        (hcoverage (Finset.mem_sdiff.mpr ⟨hw, hwe⟩))
      refine ⟨t, Finset.mem_sdiff.mpr ⟨ht, ?_⟩, htw⟩
      intro h
      exact hwout (htw ▸ (Finset.mem_filter.mp h).2)
  refine ⟨?_, ?_, ?_, ?_, hbij⟩
  · have h : (W.card : ℝ) ≤ T.card + E.card := by exact_mod_cast hlower
    linarith
  · have h : 2*(G.card : ℝ) ≤ 2*W.card + collisionCount G W F := by
      exact_mod_cast hgood
    have hT : (T.card : ℝ) = G.card + D.card := by exact_mod_cast hcardT
    linarith
  · have h : 2*((badValues G D W E F).card : ℝ) ≤
        2*E.card + 2*D.card + collisionCount G W F := by exact_mod_cast hbad
    linarith
  · exact_mod_cast hpre

end TotientAsymptotic.FiniteMap

end OAI
