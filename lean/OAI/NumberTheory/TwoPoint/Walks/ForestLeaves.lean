import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace OAI

/-! Every finite nonempty forest has a vertex with at most one neighbor. -/

namespace TwoPointCorrelations

open SimpleGraph

/-- A degree-free formulation convenient for deleting a leaf in an induction. -/
theorem finite_forest_has_leaf {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (hG : G.IsAcyclic) :
    ∃ x : V, ∀ y z : V, G.Adj x y → G.Adj x z → y = z := by
  classical
  let v : V := Classical.choice inferInstance
  let C := G.connectedComponentMk v
  have htree : C.toSimpleGraph.IsTree := hG.isTree_connectedComponent C
  let : Fintype C := Fintype.ofFinite C
  by_cases hsub : Subsingleton C
  · let : Subsingleton C := hsub
    refine ⟨v, ?_⟩
    intro y z hxy hxz
    have hyv : y = v := congrArg Subtype.val (Subsingleton.elim
      (⟨y, C.mem_supp_of_adj_mem_supp (show v ∈ C from rfl) hxy⟩ : C) ⟨v, rfl⟩)
    exact (hxy.ne hyv.symm).elim
  · let : Nontrivial C := not_subsingleton_iff_nontrivial.mp hsub
    obtain ⟨x, hx⟩ := htree.exists_vert_degree_one_of_nontrivial
    obtain ⟨p, hp, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hx
    refine ⟨x.val, ?_⟩
    intro y z hxy hxz
    let y' : C := ⟨y, C.mem_supp_of_adj_mem_supp x.property hxy⟩
    let z' : C := ⟨z, C.mem_supp_of_adj_mem_supp x.property hxz⟩
    have hy' : C.toSimpleGraph.Adj x y' := hxy
    have hz' : C.toSimpleGraph.Adj x z' := hxz
    exact congrArg Subtype.val ((huniq y' hy').trans (huniq z' hz').symm)

end TwoPointCorrelations

end OAI
