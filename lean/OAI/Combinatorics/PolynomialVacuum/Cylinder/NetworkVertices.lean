import OAI.Combinatorics.PolynomialVacuum.Cylinder.NetworkCycles

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M : ℕ}

@[simp] theorem edgeVertices_edgeOf (g : Germ M) :
    edgeVertices (edgeOf g)={g.1,neighbor g.1 g.2} := by
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;> simp [edgeOf,edgeVertices,neighbor,Finset.pair_comm]

 

theorem traced_edge_vertices (g : Germ M) (w : List Bool) :
    (tracedEdges g w).biUnion edgeVertices ∪ {g.1}=
      (traced g w).toFinset ∪ {(terminalGerm g w).1} := by
  induction w generalizing g with
  | nil => simp [tracedEdges,traced,terminalGerm]
  | cons b w ih =>
    simp only [tracedEdges,Finset.biUnion_insert,edgeVertices_edgeOf,
      traced,List.toFinset_cons,terminalGerm]
    have hh:=ih (advance g b)
    ext v
    have hv:=congrArg (fun S : Finset (Vertex M) => v∈S) hh
    simp only [Finset.mem_union,Finset.mem_singleton,Finset.mem_insert,advance] at hv ⊢
    tauto

theorem closed_traced_edge_vertices (g : Germ M) (w : List Bool)
    (hne : w≠[]) (hc : terminalGerm g w=g) :
    (tracedEdges g w).biUnion edgeVertices=(traced g w).toFinset := by
  have hroot : g.1∈(traced g w).toFinset := by
    obtain ⟨b,u,rfl⟩:=List.exists_cons_of_ne_nil hne
    simp [traced]
  have hedge : g.1∈(tracedEdges g w).biUnion edgeVertices := by
    obtain ⟨b,u,rfl⟩:=List.exists_cons_of_ne_nil hne
    simp only [tracedEdges,Finset.biUnion_insert,edgeVertices_edgeOf]
    exact Finset.mem_union_left _ (by simp)
  have hh:=traced_edge_vertices g w
  simpa [hc,Finset.insert_eq_of_mem hroot,Finset.insert_eq_of_mem hedge] using hh

namespace ClosedNetwork
variable (C : ClosedNetwork M)

theorem polygon_vertices (v : C.sites) :
    (C.polygon v).vertices=(List.range (C.period v)).toFinset.image (fun k => (C.next^[k] v).val) := by
  change (tracedEdges (C.germ v) (C.word (C.period v) v)).biUnion edgeVertices=_
  have hn : C.word (C.period v) v≠[] := by
    intro h
    have hh:=congrArg List.length h
    have hz : C.period v=0 := by simpa using hh
    exact (C.period_pos v).ne' hz
  rw [closed_traced_edge_vertices _ _ hn (C.orbit_terminal v),C.traced_word]
  ext u
  simp

theorem next_ne (v : C.sites) : C.next v≠v := by
  intro h
  have hi:=C.incident v
  rw [h] at hi
  cases hv : v.val <;> simp only [hv] at hi <;>
    simp only [neighbor] at hi <;> split_ifs at hi

theorem mem_polygon_vertices (v u : C.sites) :
    u.val∈(C.polygon v).vertices ↔ C.next.SameCycle v u := by
  rw [C.polygon_vertices]
  constructor
  · intro h
    obtain ⟨k,hk,he⟩:=Finset.mem_image.mp h
    have he' : C.next^[k] v=u := Subtype.ext he
    refine ⟨(k : ℤ),?_⟩
    simpa only [zpow_natCast,Equiv.Perm.coe_pow] using he'
  · intro hs
    obtain ⟨k,_,hk⟩:=hs.exists_pow_eq'
    refine Finset.mem_image.mpr ⟨k % C.period v,by simpa using Nat.mod_lt k (C.period_pos v),?_⟩
    rw [show C.period v=Function.minimalPeriod C.next v from rfl,Function.iterate_mod_minimalPeriod_eq]
    simpa only [Equiv.Perm.coe_pow] using congrArg Subtype.val hk

theorem polygon_vertices_subset (v : C.sites) : (C.polygon v).vertices⊆C.sites := by
  intro u hu
  rw [C.polygon_vertices] at hu
  obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp hu
  exact (C.next^[k] v).property

end ClosedNetwork
end PolynomialVacuumCylinder

end OAI
