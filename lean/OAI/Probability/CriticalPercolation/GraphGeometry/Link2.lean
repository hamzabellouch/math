import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.HitEvent
import OAI.Probability.CriticalPercolation.GraphGeometry.VertexBall
import OAI.Probability.CriticalPercolation.GraphGeometry.Link

namespace OAI

section
section CurrentModule1
noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
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

end Wiring

open ClusterDeletion

variable {V E : Type*} (G : BondGraph V E)

def reachesTarget (o : V) (T : Set V) (ω : Set E) : Prop :=
  o ∈ roots (G.openGraph ω) T

lemma reachesTarget_mono (o : V) (T : Set V) {ω ω' : Set E}
    (h : ω ⊆ ω') : reachesTarget G o T ω → reachesTarget G o T ω' :=
  fun ho => roots_mono (G.openGraph_mono h) T ho

lemma reachesTarget_iff_hitEvent (o : V) (T : Set V) (ω : Set E) :
    reachesTarget G o T ω ↔ ω ∈ G.hitEvent o T := by
  constructor
  · rintro ⟨t, ht, hto⟩
    exact ⟨t, hto.symm, ht⟩
  · rintro ⟨t, hot, ht⟩
    exact ⟨t, ht, hot.symm⟩

def boundaryReach (R : Set V) (H : SimpleGraph V) (o : V) (e : E) : Prop :=
  ∃ x y, G.ends e = s(x,y) ∧ x ∉ R ∧ y ∈ R ∧ H.Reachable o x

lemma openGraph_force_true (ω : Set E) (e : E) (v b : V)
    (he : G.ends e = s(v,b)) :
    G.openGraph (Function.update ω e True) = G.openGraph ω ⊔ SimpleGraph.edge v b := by
  have hs : (Function.update ω e True : Set E) = insert e ω := by
    ext j
    by_cases hje : j = e
    · subst j; erw [Function.update_self]; exact iff_of_true trivial (Set.mem_insert e ω)
    · erw [Function.update_of_ne hje]
      change j ∈ ω ↔ j ∈ insert e ω
      simp [hje]
  erw [hs]
  rw [BondGraph.openGraph,Set.image_insert_eq,he,← Set.singleton_union,SimpleGraph.fromEdgeSet_union]
  exact sup_comm _ _

lemma target_creating_iff (o : V) (T : Set V) (ω : Set E) (e : E)
    (ho : ¬ reachesTarget G o T ω) :
    reachesTarget G o T (Function.update ω e True) ↔
      boundaryReach G (roots (G.openGraph ω) T)
        (delete (G.openGraph ω) (roots (G.openGraph ω) T)) o e := by
  let H := G.openGraph ω
  let R := roots H T
  have hor : o ∉ R := ho
  have hdel : component (delete H R) o = component H o :=
    delete_roots_component H T o hor
  constructor
  · intro hn
    obtain ⟨⟨a,b⟩,hab⟩ := Sym2.mk_surjective (G.ends e)
    have he : G.ends e = s(a,b) := hab.symm
    obtain ⟨t,ht,hnew⟩ := hn
    rw [openGraph_force_true G ω e a b he] at hnew
    have hh := (Wiring.reachable_sup_edge H a b o t).mp hnew.symm
    rcases hh with hold | ⟨hoa,hbt⟩ | ⟨hob,hat⟩
    · exact (ho ⟨t,ht,hold.symm⟩).elim
    · refine ⟨a,b,he,reachable_not_mem_roots hor hoa,⟨t,ht,hbt.symm⟩,?_⟩
      change a ∈ component (delete H R) o
      rw [hdel]
      exact hoa
    · refine ⟨b,a,?_,reachable_not_mem_roots hor hob,⟨t,ht,hat.symm⟩,?_⟩
      · simpa only [Sym2.eq_swap] using he
      · change b ∈ component (delete H R) o
        rw [hdel]
        exact hob
  · rintro ⟨x,y,he,hx,⟨t,ht,hty⟩,hox⟩
    refine ⟨t,ht,?_⟩
    rw [openGraph_force_true G ω e x y he]
    apply SimpleGraph.Reachable.symm
    apply (Wiring.reachable_sup_edge (G.openGraph ω) x y o t).mpr
    exact Or.inr (Or.inl ⟨hox.mono (delete_le _ _),hty.symm⟩)

lemma boundaryReach_closed (o : V) (T : Set V) (ω : Set E) (e : E)
    (h : boundaryReach G (roots (G.openGraph ω) T)
      (delete (G.openGraph ω) (roots (G.openGraph ω) T)) o e) : ¬ ω e := by
  rintro heω
  obtain ⟨x,y,he,hx,hy,_⟩ := h
  have hxy : x ≠ y := fun heq => hx (heq ▸ hy)
  have ha : (G.openGraph ω).Adj y x := by
    apply SimpleGraph.Adj.symm
    exact ⟨⟨e,heω,he⟩,hxy⟩
  exact hx (roots_closed hy ha)

end CriticalPercolation.Sharpness
end
end CurrentModule1

end

end OAI
