import Mathlib

namespace OAI

/-!
Scarf incidence argument used to prove the fixed point principle needed
for the simultaneous normalization. In spirit cf. Ivanov "Beyond Sperner's
lemma". Here we use labels as extra ghost vertices so facets can use
ordinary Finset inclusion.
-/

noncomputable section
open Finset
namespace GeneralMahler.Scarf
variable {I T : Type*} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

structure Orders (I T : Type*) where
  rank : I → T → ℕ
  inj : ∀ i, Function.Injective (rank i)
variable (r : Orders I T)

-- dominance formulated without choosing minima
def dom (s : Finset T) : Prop :=
  ∀ x : T, ∃ i:I, ∀ y∈s, r.rank i x ≤ r.rank i y

omit [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T] in
lemma dom_subset {s d : Finset T} (h : d ⊆ s) (hd : dom r s) :
    dom r d := fun x => by
      obtain ⟨i,he⟩ := hd x
      exact ⟨i,fun y hy => he y (h hy)⟩

omit [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T] in
lemma min_nodes {s : Finset T} (hs : s.Nonempty) :
    ∃ u : I → T, ∀ i, u i ∈ s ∧ ∀ x∈s, r.rank i (u i) ≤ r.rank i x := by
  have h (i : I) := Finset.exists_min_image s (r.rank i) hs
  choose u he hu using h
  exact ⟨u,fun i=>⟨he i,hu i⟩⟩

omit [DecidableEq I] [Fintype T] in
lemma min_cover {s : Finset T} (hs : dom r s) {u : I→T}
    (h : ∀ i, u i ∈ s ∧ ∀ x∈s, r.rank i (u i) ≤ r.rank i x) :
    univ.image u = s := by
  ext x
  constructor
  · intro hx
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hx
    subst x; exact (h i).1
  · intro hx
    obtain ⟨i,hi⟩ := hs x
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,
      r.inj i (le_antisymm ((h i).2 _ hx) (hi _ (h i).1))⟩

variable {A B : Type*} [DecidableEq A] [DecidableEq B]
lemma image_erase_eq' {s:Finset A} {u : A→B} {a b : A}
    (hb:b∈s) (hne:a≠b) (he:u a=u b) :
    (s.erase a).image u = s.image u := by
  ext y
  simp only [Finset.mem_image,Finset.mem_erase]
  constructor
  · rintro ⟨i,⟨-,hi⟩,he⟩; exact ⟨i,hi,he⟩
  · rintro ⟨i,hi,hd⟩
    by_cases hu:i=a
    · subst i; exact ⟨b,⟨Ne.symm hne,hb⟩,he.symm.trans hd⟩
    · exact ⟨i,⟨hu,hi⟩,hd⟩

-- unique pair of repeated indices of a map onto one-less elements
lemma duplicate_pair {s:Finset A} (u : A→B)
    (h : s.card = (s.image u).card+1) :
    ∃ a ∈ s, ∃ b ∈ s, a≠b ∧ u a=u b ∧
      ∀ i ∈ s, ∀ j ∈ s, i≠j → u i=u j → (i=a ∧ j=b) ∨ (i=b ∧ j=a) := by
  obtain ⟨a,ha,b,hb,hab,he⟩ := exists_ne_map_eq_of_card_image_lt (f := u) (s := s) (by omega)
  have H (a b : A) (ha:a∈s) (hb:b∈s) (hab:a≠b) (he:u a=u b) :
      Set.InjOn u (↑(s.erase a)) := injOn_of_card_image_eq (by
        rw [image_erase_eq' hb hab he, card_erase_of_mem ha]; omega)
  refine ⟨a,ha,b,hb,hab,he,?_⟩
  intro i hi j hj hij heq
  have H₁ := H a b ha hb hab he
  have H₂ := H b a hb ha (Ne.symm hab) he.symm
  have heither (a:A) (H:Set.InjOn u (↑(s.erase a))) : i=a ∨ j=a := by
    by_contra! h
    exact hij (H (mem_erase.mpr ⟨h.1,hi⟩) (mem_erase.mpr ⟨h.2,hj⟩) heq)
  rcases heither a H₁ with h|h <;> rcases heither b H₂ with h'|h' <;> grind

section Door
variable (d : Finset T)
def room (s : Finset T) := s.card = Fintype.card I ∧ dom r s
def door := Fintype.card I = d.card+1 ∧ dom r d
variable {d}
-- candidate replacements for each repeated index
def cand (u : I → T) (i : I) := Finset.univ.filter fun x =>
    ∀ j:I, j ≠ i → r.rank j (u j)<r.rank j x

omit [DecidableEq T] in
lemma mem_cand' {u : I → T} {i : I} {x : T} :
    x∈cand r u i ↔ ∀ j:I, j≠i → r.rank j (u j)<r.rank j x := by simp [cand]

lemma extension_spec {d : Finset T} {u : I → T} {x : T}
    (hd : door r d) (hm : ∀ i, u i ∈ d ∧ ∀ x∈d, r.rank i (u i) ≤ r.rank i x) :
    (x∉d ∧ room r (insert x d)) ↔
      ∃ i:I, (∃ j, i≠j ∧ u i=u j) ∧ x ∈ cand r u i ∧
        ∀ y ∈ cand r u i, r.rank i y ≤ r.rank i x := by
  have hh := min_cover r hd.2 hm
  constructor
  · rintro ⟨hx,hc,H⟩
    obtain ⟨v,hmin⟩ := min_nodes r (Finset.insert_nonempty x d)
    have heq := min_cover r H hmin
    have hi : Set.InjOn v (↑(univ : Finset I)) := injOn_of_card_image_eq (by rw [heq,hc,card_univ])
    have hu : x ∈ (univ.image v) := by rw [heq]; exact mem_insert_self ..
    obtain ⟨i,-,he⟩ := Finset.mem_image.mp hu
    have hv (j) (hj:j≠i) : u j=v j ∧ r.rank j (u j)<r.rank j x := by
      have hne : v j ≠ x := fun h' => hj (hi (Finset.mem_univ _) (Finset.mem_univ _) (h'.trans he.symm))
      have hmj : v j∈d := (mem_insert.mp (hmin j).1).resolve_left hne
      have eq := r.inj j (le_antisymm ((hm j).2 _ hmj)
        ((hmin j).2 _ (mem_insert_of_mem (hm j).1)))
      rw [eq]
      exact ⟨rfl, lt_of_le_of_ne ((hmin j).2 _ (mem_insert_self ..)) (fun HH=>hne (r.inj j HH))⟩
    have hh' : u i ∈ univ.image v := heq.symm ▸ mem_insert_of_mem (hm i).1
    obtain ⟨j,-,hj⟩ := Finset.mem_image.mp hh'
    have hn : j ≠ i := by intro h; apply hx; rw [← he,← h,hj]; apply (hm i).1
    refine ⟨i,⟨j,Ne.symm hn,hj.symm.trans (hv j hn).1.symm⟩,
      (mem_cand' r).mpr (fun j h => (hv j h).2),fun y hy => ?_⟩
    obtain ⟨k,Hk⟩ := H y
    by_cases hk : k=i
    · subst k; exact Hk x (mem_insert_self ..)
    · exact False.elim ((not_lt_of_ge (Hk (u k) (mem_insert_of_mem (hm k).1))) ((mem_cand' r).mp hy k hk))
  · rintro ⟨i,⟨j,hne,hij⟩,hc,H⟩
    have hh₁ := (mem_cand' r).mp hc
    have hx : x∉d := by
      intro hx
      obtain ⟨l,hl⟩ := hd.2 x
      by_cases h:l=i
      · subst l
        have he := r.inj i (le_antisymm (hl _ (hm i).1) ((hm i).2 _ hx))
        have hp := hh₁ j (Ne.symm hne)
        rw [he,hij] at hp; exact lt_irrefl _ hp
      · exact not_lt_of_ge (hl _ (hm l).1) (hh₁ l h)
    have hk : r.rank i x ≤ r.rank i (u i) := by
      obtain ⟨l,hl⟩ := hd.2 x
      by_cases h:l=i
      · subst l; exact hl _ (hm i).1
      · exact False.elim (not_lt_of_ge (hl _ (hm l).1) (hh₁ l h))
    refine ⟨hx,by rw [card_insert_of_notMem hx, hd.1], fun y => ?_⟩
    by_cases hy : y ∈ cand r u i
    · refine ⟨i,?_⟩
      intro t ht
      rcases mem_insert.mp ht with h|h
      · subst t; exact H _ hy
      · exact (H _ hy).trans (hk.trans ((hm i).2 _ h))
    · rw [mem_cand'] at hy
      push Not at hy
      obtain ⟨l,hl,he⟩ := hy
      refine ⟨l,?_⟩
      intro t ht
      rcases mem_insert.mp ht with h|h
      · subst t; exact he.trans (hh₁ _ hl).le
      · exact he.trans ((hm l).2 _ h)
end Door
end GeneralMahler.Scarf

end

end OAI
