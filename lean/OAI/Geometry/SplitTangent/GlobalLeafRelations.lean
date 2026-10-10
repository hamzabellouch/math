import Mathlib
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.PositiveTangentCurves
import OAI.Geometry.SplitTangent.RationalCurveFrames
import OAI.Geometry.SplitTangent.BoxRelationLocus
import OAI.Geometry.SplitTangent.DenseCompactLeaves
import OAI.Geometry.SplitTangent.LeafRank
import OAI.Geometry.SplitTangent.LeafPlaques

namespace OAI

/-! Global Leaf Relations. -/

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold BigOperators
universe u
namespace SplitTangent.RationalCurveFrames
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  {e : ProjectiveEmbedding X} {g : RationalCurve X} (F : RationalCurveFrames e g)
  (L : LeafJetAtlas S)
include F in
lemma exists_boxRelationLocus_of_rank {r : ℕ}
    (hr : Module.finrank ℂ (S.first (g.finite 1))=r)
    (ht : g.TangentTo S.first) (hg : PointedGenerated g S.first)
    (D : MvPolynomial.homogeneousSubmodule (Fin (e.N+1)) ℂ 1)
    (H : Fin (r+1) → MvPolynomial.homogeneousSubmodule (Fin (e.N+1)) ℂ 1) :
    ∃t,g.finite 1∈L.boxRelationLocus e D H t := by
  subst r
  exact F.exists_boxRelationLocus L ht hg D H
end SplitTangent.RationalCurveFrames
namespace SplitTangent.LeafJetAtlas
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  [CompactSpace X.Carrier] [ConnectedSpace X.Carrier]
  (L : LeafJetAtlas S) (e : ProjectiveEmbedding X)

 

theorem exists_uniform_boxRelationLocus (hRC : RationallyConnected e) (hdim : 0<X.dim)
    (x : X.Carrier)
    (D : MvPolynomial.homogeneousSubmodule (Fin (e.N+1)) ℂ 1)
    (H : Fin (Module.finrank ℂ (S.first x)+1) →
      MvPolynomial.homogeneousSubmodule (Fin (e.N+1)) ℂ 1) :
    ∃t,L.boxRelationLocus e D H t=univ := by
  classical
  have hcover : interior S.positiveLocus ⊆ ⋃t,L.boxRelationLocus e D H t := by
    intro y hy
    obtain ⟨g,he,ht,hg⟩ := interior_subset hy
    obtain ⟨F⟩ := g.exists_frames e
    obtain ⟨t,ht⟩ := F.exists_boxRelationLocus_of_rank L (L.first_rank_eq (g.finite 1) x) ht hg D H
    exact mem_iUnion.mpr ⟨t,he ▸ ht⟩
  have hd : Dense (⋃t,interior (L.boxRelationLocus e D H t)) :=
    isOpen_interior.isGδ.dense_iUnion_interior_of_closed
      (S.dense_interior_positiveLocus e hRC hdim)
      (fun t => (L.boxRelationLocus_locally_holomorphic e D H t).isClosed) hcover
  obtain ⟨z,hz⟩ := hd.nonempty
  obtain ⟨t,ht⟩ := mem_iUnion.mp hz
  exact ⟨t,L.commonZeros_eq_univ (L.boxRelationLocus_locally_holomorphic e D H t) ⟨z,ht⟩⟩

 

theorem all_leaf_closure_relation (hRC : RationallyConnected e) (hdim : 0<X.dim)
    (x : X.Carrier)
    (D : MvPolynomial.homogeneousSubmodule (Fin (e.N+1)) ℂ 1)
    (H : Fin (Module.finrank ℂ (S.first x)+1) →
      MvPolynomial.homogeneousSubmodule (Fin (e.N+1)) ℂ 1) :
    ∃p : MvPolynomial (Fin (Module.finrank ℂ (S.first x)+1)) ℂ,p≠0 ∧
      ∀z∈closure (L.leaf x),MvPolynomial.eval (e.map z).rep D.val≠0 →
        MvPolynomial.eval (fun i => MvPolynomial.eval (e.map z).rep (H i).val /
          MvPolynomial.eval (e.map z).rep D.val) p=0 := by
  obtain ⟨t,ht⟩ := L.exists_uniform_boxRelationLocus e hRC hdim x D H
  exact L.boxRelationLocus_affine e D H (ht ▸ Set.mem_univ x)

end SplitTangent.LeafJetAtlas

end

end OAI
