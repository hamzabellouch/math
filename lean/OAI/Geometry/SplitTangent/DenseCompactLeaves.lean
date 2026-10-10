import Mathlib
import OAI.Geometry.SplitTangent.BracketIntegrability
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.PositiveTangentCurves
import OAI.Geometry.SplitTangent.OpenPositiveLeaves
import OAI.Geometry.SplitTangent.DenseRationalVariation

namespace OAI

/-! Dense Compact Leaves. -/

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold
universe u
namespace SplitTangent.TangentSplitting
variable {X : ComplexManifold.{u}} [CompactSpace X.Carrier]
  (S : TangentSplitting X) (e : ProjectiveEmbedding X)

def positiveLocus : Set X.Carrier := {x | ∃g : RationalCurve X,
  g.finite 1=x ∧ g.TangentTo S.first ∧ PointedGenerated g S.first}

include e in
lemma submersive_range_positive {T : ComplexManifold.{u}} (G : RationalFamily X T)
    (hs : ∀τ,Function.Surjective (mfderiv (ModelWithCorners T)
      ((ModelWithCorners X).prod (ModelWithCorners X)) (G.twoPointEvaluation 0 1) τ)) :
    Set.range (G.evaluation 1) ⊆ S.positiveLocus := by
  rintro x ⟨τ,rfl⟩
  obtain ⟨B⟩ := S.exists_projective_tangent_box e (G.curve τ)
  exact ⟨B.firstFactor 1,B.firstFactor_diagonal 1,B.firstFactor_tangentTo 1,
    B.firstFactor_pointedGenerated (G.pointedGenerated_of_submersive S τ (hs τ))⟩

lemma dense_interior_positiveLocus (hRC : RationallyConnected e) (hdim : 0<X.dim) :
    Dense (interior S.positiveLocus) := by
  rw [dense_iff_inter_open]
  intro V hV hVn
  let V₂ : Set (X.Carrier × X.Carrier) := Set.univ ×ˢ V
  have hV₂ : IsOpen V₂ := isOpen_univ.prod hV
  obtain ⟨v,hv⟩ := hVn
  have hV₂n : V₂.Nonempty := ⟨(v,v),Set.mem_univ _,hv⟩
  obtain ⟨T,hT,G,hGV,hs⟩ := hRC.exists_submersive_family_in_open e hdim V₂ hV₂ hV₂n
  let := hT
  let τ : T.Carrier := Classical.arbitrary _
  have hsub : Set.range (G.evaluation 1) ⊆ interior S.positiveLocus :=
    interior_maximal (S.submersive_range_positive e G hs) ((G.evaluation_open hs).isOpen_range)
  exact ⟨G.evaluation 1 τ,(hGV τ).2,hsub ⟨τ,rfl⟩⟩

 

theorem exists_dense_open_compact_leaves [ConnectedSpace X.Carrier]
    (hRC : RationallyConnected e) (hdim : 2≤X.dim) :
    ∃L : LeafJetAtlas S,∃U : Set X.Carrier,IsOpen U ∧ Dense U ∧
      ∀x∈U,IsCompact (L.leaf x) ∧
        (∀y∈L.leaf x,L.plaques.LocallySinglePlaque (L.leaf x) y) ∧
        ∃g : RationalCurve X,g.finite 1=x ∧ g.TangentTo S.first ∧ PointedGenerated g S.first := by
  obtain ⟨hI₁,hI₂⟩ := S.integrable_of_rationallyConnected e hRC hdim
  let L := S.leafJetAtlas hI₁ hI₂
  refine ⟨L,interior S.positiveLocus,isOpen_interior,
    S.dense_interior_positiveLocus e hRC (by omega),?_⟩
  intro x hx
  obtain ⟨g,he,ht,hp⟩ := interior_subset hx
  obtain ⟨F⟩ := g.exists_frames e
  refine ⟨?_,?_,g,he,ht,hp⟩
  · rw [←he]
    exact F.leaf_isCompact L ht hp
  · rw [←he]
    exact F.leaf_locallySinglePlaque L ht hp

end SplitTangent.TangentSplitting

end

end OAI
