import Mathlib

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation
namespace Wiring
variable {V : Type*} (H : SimpleGraph V)

def link (s b u v : V) : Prop :=
  H.Reachable u v ∨ (H.Reachable u s ∧ H.Reachable b v) ∨
    (H.Reachable u b ∧ H.Reachable s v)

lemma link_refl (s b u : V) : link H s b u u := Or.inl (.refl _)

lemma link_symm {s b u v : V} : link H s b u v → link H s b v u := by
  rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr ⟨h2.symm,h1.symm⟩)
  · exact Or.inr (Or.inl ⟨h2.symm,h1.symm⟩)

lemma link_trans {s b u v z : V} : link H s b u v → link H s b v z → link H s b u z := by
  rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩) (k | ⟨k1,k2⟩ | ⟨k1,k2⟩)
  · exact Or.inl (h.trans k)
  · exact Or.inr (Or.inl ⟨h.trans k1,k2⟩)
  · exact Or.inr (Or.inr ⟨h.trans k1,k2⟩)
  · exact Or.inr (Or.inl ⟨h1,h2.trans k⟩)
  · exact Or.inr (Or.inl ⟨h1,k2⟩)
  · exact Or.inl (h1.trans k2)
  · exact Or.inr (Or.inr ⟨h1,h2.trans k⟩)
  · exact Or.inl (h1.trans k2)
  · exact Or.inr (Or.inr ⟨h1,k2⟩)

lemma edge_reachable (s b : V) : (SimpleGraph.edge s b).Reachable s b := by
  rcases eq_or_ne s b with rfl | h
  · exact .refl _
  · exact SimpleGraph.Adj.reachable ((SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,h⟩)

theorem reachable_sup_edge (s b u v : V) :
    (H ⊔ SimpleGraph.edge s b).Reachable u v ↔ link H s b u v := by
  constructor
  · intro h
    have h' := ((H ⊔ SimpleGraph.edge s b).reachable_iff_reflTransGen u v).mp h
    clear h
    induction h' with
    | refl => exact link_refl H s b u
    | @tail z v _ hz ih =>
      apply link_trans H ih
      rcases hz with hz | hz
      · exact Or.inl hz.reachable
      · rcases ((SimpleGraph.edge_adj _ _ _ _).mp hz).1 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact Or.inr (Or.inl ⟨.refl _,.refl _⟩)
        · exact Or.inr (Or.inr ⟨.refl _,.refl _⟩)
  · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
    · exact h.mono le_sup_left
    · exact (h1.mono le_sup_left).trans ((edge_reachable s b).mono le_sup_right |>.trans
        (h2.mono le_sup_left))
    · exact (h1.mono le_sup_left).trans ((edge_reachable s b).symm.mono le_sup_right |>.trans
        (h2.mono le_sup_left))

lemma wired_pivot (a s t b : V) :
    ((H ⊔ SimpleGraph.edge a s ⊔ SimpleGraph.edge s b).Reachable a t ∧
      ¬(H ⊔ SimpleGraph.edge a s).Reachable a t) ↔
    (¬H.Reachable a t ∧ ¬H.Reachable s t ∧ H.Reachable b t) := by
  have hs : (H ⊔ SimpleGraph.edge a s).Reachable a s := (edge_reachable a s).mono le_sup_right
  rw [reachable_sup_edge]
  constructor
  · rintro ⟨hnew,hold⟩
    have ha : ¬H.Reachable a t := fun h => hold (h.mono le_sup_left)
    have hst : ¬H.Reachable s t := fun h => hold (hs.trans (h.mono le_sup_left))
    have hb : (H ⊔ SimpleGraph.edge a s).Reachable b t := by
      rcases hnew with h | ⟨_,h⟩ | ⟨_,h⟩
      · exact (hold h).elim
      · exact h
      · exact (hold (hs.trans h)).elim
    have hbt : H.Reachable b t := by
      rcases (reachable_sup_edge H a s b t).mp hb with h | ⟨_,h⟩ | ⟨_,h⟩
      · exact h
      · exact (hst h).elim
      · exact (ha h).elim
    exact ⟨ha,hst,hbt⟩
  · rintro ⟨ha,hst,hbt⟩
    constructor
    · exact Or.inr (Or.inl ⟨hs,hbt.mono le_sup_left⟩)
    · intro h
      rcases (reachable_sup_edge H a s a t).mp h with h | ⟨_,h⟩ | ⟨_,h⟩
      · exact ha h
      · exact hst h
      · exact ha h

lemma two_pivots (a s t b : V) :
    ((H ⊔ SimpleGraph.edge a s ⊔ SimpleGraph.edge s b).Reachable a t ∧
      ¬(H ⊔ SimpleGraph.edge a s).Reachable a t ∧
      ¬(H ⊔ SimpleGraph.edge s b).Reachable a t) ↔
    (¬H.Reachable a s ∧ ¬H.Reachable a t ∧ ¬H.Reachable s t ∧ H.Reachable b t) := by
  constructor
  · rintro ⟨h,he,hf⟩
    obtain ⟨hat,hst,hbt⟩ := (wired_pivot H a s t b).mp ⟨h,he⟩
    refine ⟨?_,hat,hst,hbt⟩
    intro has
    apply hf
    exact (reachable_sup_edge H s b a t).mpr (Or.inr (Or.inl ⟨has,hbt⟩))
  · rintro ⟨has,hat,hst,hbt⟩
    obtain ⟨h,he⟩ := (wired_pivot H a s t b).mpr ⟨hat,hst,hbt⟩
    refine ⟨h,he,?_⟩
    intro hf
    rcases (reachable_sup_edge H s b a t).mp hf with h | ⟨h,_⟩ | ⟨_,h⟩
    · exact hat h
    · exact has h
    · exact hst h

lemma avoid_sup_edge (a s t b : V) :
    (¬(H ⊔ SimpleGraph.edge s b).Reachable a s ∧
      ¬(H ⊔ SimpleGraph.edge s b).Reachable a t) ↔
    (¬H.Reachable a s ∧ ¬H.Reachable a t ∧ ¬H.Reachable a b) := by
  constructor
  · rintro ⟨hs,ht⟩
    refine ⟨fun h => hs (h.mono le_sup_left),fun h => ht (h.mono le_sup_left),?_⟩
    intro hb
    apply hs
    exact (reachable_sup_edge H s b a s).mpr (Or.inr (Or.inr ⟨hb,.refl _⟩))
  · rintro ⟨hs,ht,hb⟩
    constructor
    · intro h
      rcases (reachable_sup_edge H s b a s).mp h with h | ⟨h,_⟩ | ⟨h,_⟩
      · exact hs h
      · exact hs h
      · exact hb h
    · intro h
      rcases (reachable_sup_edge H s b a t).mp h with h | ⟨h,_⟩ | ⟨h,_⟩
      · exact ht h
      · exact hs h
      · exact hb h

lemma avoid_target_sup_edge (a s t b : V) :
    (¬(H ⊔ SimpleGraph.edge s b).Reachable a s ∧
      ¬(H ⊔ SimpleGraph.edge s b).Reachable a t ∧
      (H ⊔ SimpleGraph.edge s b).Reachable s t) ↔
    ((¬H.Reachable a s ∧ ¬H.Reachable a t ∧ H.Reachable s t ∧ ¬H.Reachable a b) ∨
      (¬H.Reachable a s ∧ ¬H.Reachable a t ∧ ¬H.Reachable s t ∧ H.Reachable b t)) := by
  constructor
  · rintro ⟨hs,ht,hst⟩
    obtain ⟨has,hat,hab⟩ := (avoid_sup_edge H a s t b).mp ⟨hs,ht⟩
    by_cases hst' : H.Reachable s t
    · exact Or.inl ⟨has,hat,hst',hab⟩
    · refine Or.inr ⟨has,hat,hst',?_⟩
      rcases (reachable_sup_edge H s b s t).mp hst with h | ⟨_,h⟩ | ⟨_,h⟩
      · exact (hst' h).elim
      · exact h
      · exact (hst' h).elim
  · rintro (⟨has,hat,hst,hab⟩ | ⟨has,hat,hst,hbt⟩)
    · have hh := (avoid_sup_edge H a s t b).mpr ⟨has,hat,hab⟩
      exact ⟨hh.1,hh.2,hst.mono le_sup_left⟩
    · have hab : ¬H.Reachable a b := fun h => hat (h.trans hbt)
      have hh := (avoid_sup_edge H a s t b).mpr ⟨has,hat,hab⟩
      exact ⟨hh.1,hh.2,(reachable_sup_edge H s b s t).mpr (Or.inr (Or.inl ⟨.refl _,hbt⟩))⟩

end Wiring
end CriticalPercolation

end
end

end OAI
