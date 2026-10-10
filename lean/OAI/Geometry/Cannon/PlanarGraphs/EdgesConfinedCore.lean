import Mathlib

namespace OAI

section
section
section
noncomputable section
namespace CannonForest
open Set

theorem edges_confined_to_core {V : Type*} [Finite V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (S : Set V) (hS : (G.induce S).Preconnected)
    (hother : ∀ x∉S,∀ y,G.Adj x y → ∃ z,G.Adj x z ∧ z≠y) :
    ∀ x y,G.Adj x y → x∈S ∧ y∈S := by
  classical
  let R : SimpleGraph V := {
    Adj := fun x y=>G.Adj x y ∧ ¬(x∈S ∧ y∈S)
    symm := ⟨fun x y h=>⟨h.1.symm,fun hh=>h.2 hh.symm⟩⟩
    loopless := ⟨fun x h=>h.1.ne rfl⟩ }
  have hRG : R≤G := fun _ _ h=>h.1
  have acR := hG.anti hRG
  have unique_core {x y:V} (hx:x∈S) (hy:y∈S) (hxy:R.Reachable x y) : x=y := by
    by_contra hn
    obtain ⟨p,hp⟩ := hxy.exists_isPath
    obtain ⟨q,hq⟩ := (hS ⟨x,hx⟩ ⟨y,hy⟩).exists_isPath
    let f : G.induce S →g G := ⟨Subtype.val,fun h=>h⟩
    have he : p.mapLe hRG=q.map f := Subtype.mk.inj
      (hG.subsingleton_path x y |>.elim ⟨_,hp.mapLe hRG⟩ ⟨_,hq.map Subtype.val_injective⟩)
    have hs : ∀ z∈p.support,z∈S := by
      intro z hz
      have hz' : z∈(p.mapLe hRG).support := by simpa using hz
      rw [he,SimpleGraph.Walk.support_map] at hz'
      obtain ⟨w,-,rfl⟩ := List.mem_map.mp hz'
      exact w.property
    have hpne : ¬p.Nil := SimpleGraph.Walk.not_nil_of_ne hn
    exact (p.adj_snd hpne).2 ⟨hx,hs _ (List.mem_of_mem_tail (p.snd_mem_tail_support hpne))⟩
  have hempty : R=⊥ := by
    ext x y
    constructor
    · intro hxy
      let c := R.connectedComponentMk x
      let a : c.supp := ⟨x,rfl⟩
      let b : c.supp := ⟨y,SimpleGraph.ConnectedComponent.sound hxy.reachable.symm⟩
      have hab : a≠b := fun h=>hxy.ne (congrArg Subtype.val h)
      let _ : Nontrivial c.supp := ⟨⟨a,b,hab⟩⟩
      let _ : Fintype c.supp := Fintype.ofFinite c.supp
      obtain ⟨u,v,huv,hu,hv⟩ := (acR.isTree_connectedComponent c).exists_ne_and_degree_eq_one
      have leaves (z : c.supp) (hz : c.toSimpleGraph.degree z=1) : z.val∈S := by
        by_contra hn
        obtain ⟨w,hw,hunique⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hz
        have hwG : G.Adj z.val w.val := hRG hw
        obtain ⟨t,ht,htw⟩ := hother z.val hn w.val hwG
        have htR : R.Adj z.val t := ⟨ht,fun h=>hn h.1⟩
        let t' : c.supp := ⟨t,c.mem_supp_of_adj_mem_supp z.property htR⟩
        have hadj : c.toSimpleGraph.Adj z t' := htR
        exact htw (congrArg Subtype.val (hunique _ hadj))
      have huvR : R.Reachable u.val v.val :=
        SimpleGraph.ConnectedComponent.exact (u.property.trans v.property.symm)
      exact huv (Subtype.ext (unique_core (leaves u hu) (leaves v hv) huvR))
    · exact False.elim
  intro x y hxy
  by_contra hn
  have h : R.Adj x y := ⟨hxy,hn⟩
  rw [hempty] at h
  exact h
end CannonForest

end
end
end
end

end OAI
