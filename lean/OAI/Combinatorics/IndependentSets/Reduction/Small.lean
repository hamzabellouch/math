import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.ExtensionLaw

namespace OAI

namespace LargeIndependentSets

section
def Small {r : ℕ} (s : ℕ) (I : Finset (Fin r)) : Prop :=
  I.Nonempty ∧ I.card ≤ s

def Separated {r : ℕ} (I J : Finset (Fin r)) : Prop :=
  ∀ i ∈ I, ∀ j ∈ J, i < j

def Aligned {r : ℕ} {M : Type} (A : Finset (Fin r) → Finset M)
    (B : Finset (Fin r)) : Prop :=
  ∃ a : M → Fin r, (∀ x, a x ∈ B) ∧
    ∀ I, I.Nonempty → I ⊆ B → ∀ x ∈ A I, a x ∈ I

structure LayerLaw (r s : ℕ) where
  weight : Finset (Fin r) → ℚ
  nonneg : ∀ B, 0 ≤ weight B
  total : ∑ B, weight B = 1
  support : ∀ B, B.card ≠ s → weight B = 0

noncomputable def LayerLaw.badMass {r s : ℕ} (μ : LayerLaw r s)
    {M : Type} (A : Finset (Fin r) → Finset M) : ℚ := by
  classical
  exact ∑ B, if Aligned A B then 0 else μ.weight B

def DistributionalAlignment : Prop :=
  ∀ s d : ℕ, 1 ≤ s → 1 ≤ d → ∀ η : ℝ, 0 < η →
    ∃ r : ℕ, s ≤ r ∧ ∃ μ : LayerLaw r s,
      ∀ (M : Type) [DecidableEq M] (A : Finset (Fin r) → Finset M),
        (∀ I, Small s I → (A I).card ≤ d) →
        (∀ I J, Small s I → Small s J → Separated I J → Disjoint (A I) (A J)) →
        (μ.badMass A : ℝ) ≤ η

open scoped Classical BigOperators

noncomputable def actualSlot {s d r : ℕ} {M : Type*}
    (A : Finset (Fin r) → Finset M) (a : ListSlot s d (Fin r)) : Option M :=
  if h : a.2.val < (A a.1.val).card then
    some ((A a.1.val).equivFin.symm ⟨a.2.val, h⟩).val else none

lemma actualSlot_some_mem {s d r : ℕ} {M : Type*}
    (A : Finset (Fin r) → Finset M) (a : ListSlot s d (Fin r)) (x : M)
    (h : actualSlot A a = some x) : x ∈ A a.1.val := by
  unfold actualSlot at h
  split_ifs at h with ha
  · have he := Option.some.inj h
    exact he ▸ ((A a.1.val).equivFin.symm ⟨a.2.val, ha⟩).property

lemma actualSlot_unique {s d r : ℕ} {M : Type*}
    (A : Finset (Fin r) → Finset M) (a b : ListSlot s d (Fin r))
    (hI : a.1 = b.1) (he : actualSlot A a = actualSlot A b)
    (ha : actualSlot A a ≠ none) : a.2 = b.2 := by
  obtain ⟨I, i⟩ := a
  obtain ⟨J, j⟩ := b
  dsimp at hI
  subst J
  unfold actualSlot at he ha
  split_ifs at he with hi hj
  · apply Fin.ext
    have h := (A I.val).equivFin.symm.injective (Subtype.ext (Option.some.inj he))
    exact congrArg (fun z : Fin (A I.val).card => z.val) h
  · exact False.elim (ha (by simp [hi]))

lemma actualSlot_exists {s d r : ℕ} {M : Type*}
    (A : Finset (Fin r) → Finset M) (hbound : ∀ I, Small s I → (A I).card ≤ d)
    (I : ListIndex s (Fin r)) (x : M) (hx : x ∈ A I.val) :
    ∃ i : Fin d, actualSlot A (I, i) = some x := by
  let k := (A I.val).equivFin ⟨x, hx⟩
  have hk : k.val < d := k.isLt.trans_le (hbound I.val I.property)
  refine ⟨⟨k.val, hk⟩, ?_⟩
  simp only [actualSlot, k.isLt, dite_eq_left]
  exact congrArg (fun y : A I.val => some y.val) ((A I.val).equivFin.symm_apply_apply ⟨x, hx⟩)

noncomputable def actualPattern {s d r : ℕ} {M : Type*}
    (A : Finset (Fin r) → Finset M)
    (hsep : ∀ I J, Small s I → Small s J → Separated I J → Disjoint (A I) (A J)) :
    ListPattern s d (Fin r) :=
  ⟨fun a b => decide (actualSlot A a = actualSlot A b ∧ actualSlot A a ≠ none), by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b h
      have hh := of_decide_eq_true h
      exact decide_eq_true (And.intro hh.1.symm (hh.1 ▸ hh.2))
    · intro a b c hab hbc
      have hab' := of_decide_eq_true hab
      have hbc' := of_decide_eq_true hbc
      exact decide_eq_true ⟨hab'.1.trans hbc'.1, hab'.2⟩
    · intro a b h hab
      have hh := of_decide_eq_true h
      exact actualSlot_unique A a b hab hh.1 hh.2
    · intro a b hsep'
      apply decide_eq_false
      rintro ⟨he, hne⟩
      obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hne
      have ha := actualSlot_some_mem A a x hx
      have hb := actualSlot_some_mem A b x (he.symm.trans hx)
      exact Finset.disjoint_left.mp (hsep a.1.val b.1.val a.1.property b.1.property hsep') ha hb⟩

lemma actualPattern_eq {s d r : ℕ} {M : Type*}
    (A : Finset (Fin r) → Finset M)
    (hsep : ∀ I J, Small s I → Small s J → Separated I J → Disjoint (A I) (A J))
    (a b : ListSlot s d (Fin r)) :
    (actualPattern A hsep).val a b = true ↔
      actualSlot A a = actualSlot A b ∧ actualSlot A a ≠ none := by
  exact decide_eq_true_iff

lemma actualPattern_good_aligned {s d r : ℕ} {M : Type}
    (A : Finset (Fin r) → Finset M) (hbound : ∀ I, Small s I → (A I).card ≤ d)
    (hsep : ∀ I J, Small s I → Small s J → Separated I J → Disjoint (A I) (A J))
    (B : Finset (Fin r)) (hB : B.Nonempty) (hBs : B.card ≤ s)
    (hgood : GoodPatternOn (actualPattern (d := d) A hsep) B) : Aligned A B := by
  classical
  have hchoice (x : M) : ∃ i ∈ B, ∀ I, I.Nonempty → I ⊆ B → x ∈ A I → i ∈ I := by
    by_cases hx : ∃ I, I.Nonempty ∧ I ⊆ B ∧ x ∈ A I
    · obtain ⟨I, hI, hIB, hxI⟩ := hx
      let I' : ListIndex s (Fin r) := ⟨I, hI, (Finset.card_le_card hIB).trans hBs⟩
      obtain ⟨j, hj⟩ := actualSlot_exists A hbound I' x hxI
      have haa : (actualPattern A hsep).val (I', j) (I', j) = true :=
        (actualPattern_eq _ _ _ _).mpr ⟨rfl, by rw [hj]; exact Option.some_ne_none _⟩
      obtain ⟨i, hiB, hi⟩ := hgood (I', j) hIB haa
      refine ⟨i, hiB, ?_⟩
      intro J hJ hJB hxJ
      let J' : ListIndex s (Fin r) := ⟨J, hJ, (Finset.card_le_card hJB).trans hBs⟩
      obtain ⟨k, hk⟩ := actualSlot_exists A hbound J' x hxJ
      apply hi (J', k) hJB
      exact (actualPattern_eq _ _ _ _).mpr ⟨hj.trans hk.symm, by rw [hj]; exact Option.some_ne_none _⟩
    · obtain ⟨i, hi⟩ := hB
      exact ⟨i, hi, fun I hI hIB hxI => False.elim (hx ⟨I, hI, hIB, hxI⟩)⟩
  choose a ha harest using hchoice
  exact ⟨a, ha, fun I hI hIB x hx => harest x I hI hIB hx⟩

end

noncomputable def ListSlot.pullbackFin {s d n : ℕ} {X : Type*} [LinearOrder X]
    (B : Finset X) (hB : B.card = n) (a : ListSlot s d X) (ha : a.1.val ⊆ B) :
    ListSlot s d (Fin n) :=
  ListSlot.map (B.orderIsoOfFin hB).symm.toEmbedding (a.inside B ha)

lemma ListSlot.map_pullbackFin {s d n : ℕ} {X : Type*} [LinearOrder X]
    (B : Finset X) (hB : B.card = n) (a : ListSlot s d X) (ha : a.1.val ⊆ B) :
    ListSlot.map (B.orderEmbOfFin hB).toEmbedding (a.pullbackFin B hB ha) = a := by
  unfold pullbackFin
  rw [ListSlot.map_comp]
  have he : (B.orderIsoOfFin hB).symm.toEmbedding.trans (B.orderEmbOfFin hB).toEmbedding =
      Function.Embedding.subtype (· ∈ B) := by
    ext x
    change ((B.orderIsoOfFin hB) ((B.orderIsoOfFin hB).symm x)).val = x.val
    rw [OrderIso.apply_symm_apply]
  rw [he, ListSlot.map_inside]

lemma good_full_restrict_goodOn {s d n : ℕ} {X : Type*} [LinearOrder X]
    (C : ListPattern s d X) (B : Finset X) (hB : B.card = n)
    (hgood : GoodPatternOn (C.restrict (B.orderEmbOfFin hB)) Finset.univ) :
    GoodPatternOn C B := by
  classical
  intro a ha haa
  have hsame : (C.restrict (B.orderEmbOfFin hB)).val
      (a.pullbackFin B hB ha) (a.pullbackFin B hB ha) = true := by
    change C.val (ListSlot.map _ _) (ListSlot.map _ _) = true
    rw [ListSlot.map_pullbackFin, haa]
  obtain ⟨i, _, hi⟩ := hgood (a.pullbackFin B hB ha) (Finset.subset_univ _) hsame
  refine ⟨B.orderEmbOfFin hB i, B.orderEmbOfFin_mem hB i, ?_⟩
  intro b hb hab
  have hrel : (C.restrict (B.orderEmbOfFin hB)).val
      (a.pullbackFin B hB ha) (b.pullbackFin B hB hb) = true := by
    change C.val (ListSlot.map _ _) (ListSlot.map _ _) = true
    rw [ListSlot.map_pullbackFin, ListSlot.map_pullbackFin, hab]
  have hm := hi (b.pullbackFin B hB hb) (Finset.subset_univ _) hrel
  have hm' : B.orderEmbOfFin hB i ∈
      (ListSlot.map (B.orderEmbOfFin hB).toEmbedding (b.pullbackFin B hB hb)).1.val :=
    Finset.mem_map.mpr ⟨i, hm, rfl⟩
  rwa [ListSlot.map_pullbackFin] at hm'

lemma good_embedding_restrict_goodOn {s d n : ℕ} {X : Type*} [LinearOrder X]
    (C : ListPattern s d X) (e : Fin n ↪o X)
    (hgood : GoodPatternOn (C.restrict e) Finset.univ) :
    GoodPatternOn C (Finset.univ.map e.toEmbedding) := by
  apply good_full_restrict_goodOn (n := n) C _ (by simp)
  simpa only [finite_embedding_sorted] using hgood

end LargeIndependentSets

end OAI
