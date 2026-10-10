import Mathlib
import OAI.Geometry.SplitTangent.EmbeddedHolomorphicAtlas
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.AllCompactLeaves
import OAI.Geometry.SplitTangent.ProjectivePositiveLeaf

namespace OAI

/-! All Projective Leaves. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
universe u
namespace SplitTangent.LeafJetAtlas
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  [CompactSpace X.Carrier] [ConnectedSpace X.Carrier]
  (L : LeafJetAtlas S) (e : ProjectiveEmbedding X)
  (hRC : RationallyConnected e) (hdim : 0<X.dim)

 

def projectiveLeaf (x : X.Carrier) : ComplexManifold.{u} :=
  (L.embeddedAtlas x (L.all_leaf_locallySinglePlaque e hRC hdim x)).manifold

lemma projectiveLeaf_isProjective (x : X.Carrier) :
    IsProjective (L.projectiveLeaf e hRC hdim x) := by
  let A := L.embeddedAtlas x (L.all_leaf_locallySinglePlaque e hRC hdim x)
  exact ⟨isCompact_iff_compactSpace.mp (L.all_leaf_isCompact e hRC hdim x),
    ⟨A.projectiveEmbedding e⟩⟩

lemma projectiveLeaf_connected (x : X.Carrier) :
    ConnectedSpace (L.projectiveLeaf e hRC hdim x).Carrier :=
  isConnected_iff_connectedSpace.mp (L.plaques.leaf_isConnected x)

lemma projectiveLeaf_dim (x : X.Carrier) :
    (L.projectiveLeaf e hRC hdim x).dim=Module.finrank ℂ (S.first x) := rfl

lemma projectiveLeaf_inclusion_holomorphic (x : X.Carrier) :
    let A := L.embeddedAtlas x (L.all_leaf_locallySinglePlaque e hRC hdim x);
    letI := A.chartedSpace;
    ContMDiff 𝓘(ℂ,Fin (Module.finrank ℂ (S.first x)) → ℂ) (ModelWithCorners X) ω
      (Subtype.val : L.leaf x → X.Carrier) :=
  (L.embeddedAtlas x (L.all_leaf_locallySinglePlaque e hRC hdim x)).inclusion_holomorphic

lemma projectiveLeaf_inclusion_tangent (x : X.Carrier) :
    let A := L.embeddedAtlas x (L.all_leaf_locallySinglePlaque e hRC hdim x);
    letI := A.chartedSpace;
    ∀y : L.leaf x,LinearMap.range (mfderiv
      𝓘(ℂ,Fin (Module.finrank ℂ (S.first x)) → ℂ) (ModelWithCorners X)
      (Subtype.val : L.leaf x → X.Carrier) y).toLinearMap=S.first y.val :=
  L.embedded_inclusion_tangent x (L.all_leaf_locallySinglePlaque e hRC hdim x)

include e hRC hdim in
 
lemma projectiveLeaf_inclusion_isClosedEmbedding (x : X.Carrier) :
    IsClosedEmbedding (Subtype.val : (L.projectiveLeaf e hRC hdim x).Carrier → X.Carrier) :=
  (L.all_leaf_isClosed e hRC hdim x).isClosedEmbedding_subtypeVal

end SplitTangent.LeafJetAtlas

end

end OAI
