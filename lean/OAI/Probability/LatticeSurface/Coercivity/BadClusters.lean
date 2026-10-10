import Mathlib
import OAI.Probability.LatticeSurface.Coercivity.FilledHull
import OAI.Probability.LatticeSurface.Coercivity.GridClosedLabels
import OAI.Probability.LatticeSurface.Coercivity.HoleGeometry
import OAI.Probability.LatticeSurface.Coercivity.HoleIncident
import OAI.Probability.LatticeSurface.Coercivity.HoleStar
import OAI.Probability.LatticeSurface.Coercivity.HullMore
import OAI.Probability.LatticeSurface.Coercivity.HullRims
import OAI.Probability.LatticeSurface.Coercivity.OuterHulls

namespace OAI

noncomputable section

open scoped BigOperators

namespace SparseHoles

noncomputable def badCluster (B : Finset Vertex) (x : B) : Finset Vertex := by
  classical
  exact ((Finset.univ : Finset B).filter
    (fun y => (star.induce (B:Set Vertex)).Reachable x y)).image Subtype.val

noncomputable def badClusters (B : Finset Vertex) : Finset (Finset Vertex) := by
  classical
  exact (Finset.univ : Finset B).image (badCluster B)

lemma mem_badCluster (B : Finset Vertex) (x : B) (y : Vertex) :
    y∈badCluster B x ↔ ∃ hy : y∈B, (star.induce (B:Set Vertex)).Reachable x ⟨y,hy⟩ := by
  classical
  simp only [badCluster,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨z.property,hz⟩
  · rintro ⟨hy,hxy⟩
    exact ⟨⟨y,hy⟩,hxy,rfl⟩

lemma badCluster_self (B : Finset Vertex) (x : B) : x.val∈badCluster B x :=
  (mem_badCluster B x x).mpr ⟨x.property,SimpleGraph.Reachable.rfl⟩

lemma badCluster_subset (B : Finset Vertex) (x : B) : badCluster B x ⊆ B := by
  intro y hy
  exact ((mem_badCluster B x y).mp hy).choose

lemma badCluster_connected (B : Finset Vertex) (x : B) :
    (star.induce (badCluster B x:Set Vertex)).Connected := by
  let G := star.induce (B:Set Vertex)
  let C := G.connectedComponentMk x
  have hm : ∀ y : B, y∈C.supp ↔ y.val∈badCluster B x := by
    intro y
    rw [mem_badCluster]
    have hh : y∈C.supp ↔ G.Reachable x y := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      exact ⟨fun h => (SimpleGraph.ConnectedComponent.eq.mp h).symm,
        fun h => SimpleGraph.ConnectedComponent.eq.mpr h.symm⟩
    simpa only [hh] using (show G.Reachable x y ↔ ∃ hy:y.val∈B, G.Reachable x ⟨y.val,hy⟩ from
      ⟨fun h => ⟨y.property,h⟩,fun ⟨_,h⟩ => h⟩)
  let f : C.toSimpleGraph →g star.induce (badCluster B x:Set Vertex) :=
    ⟨fun y => ⟨y.val.val,(hm y.val).mp y.property⟩,fun h => h⟩
  apply C.connected_toSimpleGraph.map f
  rintro ⟨y,hy⟩
  have hyB := badCluster_subset B x hy
  exact ⟨⟨⟨y,hyB⟩,(hm ⟨y,hyB⟩).mpr hy⟩,rfl⟩

lemma badCluster_eq_of_reachable (B : Finset Vertex) {x y : B}
    (hxy : (star.induce (B:Set Vertex)).Reachable x y) : badCluster B x=badCluster B y := by
  ext z
  simp only [mem_badCluster]
  exact ⟨fun ⟨hz,hxz⟩ => ⟨hz,hxy.symm.trans hxz⟩,
    fun ⟨hz,hyz⟩ => ⟨hz,hxy.trans hyz⟩⟩

lemma badClusters_family (B : Finset Vertex) (lo hi : Vertex) (hB : B ⊆ box lo hi) :
    ClusterFamily (badClusters B) lo hi := by
  classical
  have horigin : ∀ C∈badClusters B, ∃ x : B, badCluster B x=C := by
    intro C hC
    simpa only [badClusters,Finset.mem_image,Finset.mem_univ,true_and] using hC
  constructor
  · intro C hC
    obtain ⟨x,rfl⟩ := horigin C hC
    exact ⟨x,badCluster_self B x⟩
  · intro C hC
    obtain ⟨x,rfl⟩ := horigin C hC
    exact (badCluster_subset B x).trans hB
  · intro C hC
    obtain ⟨x,rfl⟩ := horigin C hC
    exact badCluster_connected B x
  · intro C hC D hD hCD c hc d hd
    obtain ⟨x,rfl⟩ := horigin C hC
    obtain ⟨y,rfl⟩ := horigin D hD
    obtain ⟨hcB,hxc⟩ := (mem_badCluster B x c).mp hc
    obtain ⟨hdB,hyd⟩ := (mem_badCluster B y d).mp hd
    constructor
    · intro he
      subst d
      exact hCD (badCluster_eq_of_reachable B (hxc.trans hyd.symm))
    · intro hcd
      have hh : (star.induce (B:Set Vertex)).Adj ⟨c,hcB⟩ ⟨d,hdB⟩ := hcd
      exact hCD (badCluster_eq_of_reachable B (hxc.trans (hh.reachable.trans hyd.symm)))

end SparseHoles

end

end OAI
