import Mathlib
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.BracketIntegrability
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.PositiveTangentCurves
import OAI.Geometry.SplitTangent.CompactPositiveLeaf
import OAI.Geometry.SplitTangent.ProjectivePositiveLeaf

namespace OAI

/-! Open Positive Leaves. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
universe u
namespace SplitTangent

namespace RationalFamily
variable {X T : ComplexManifold.{u}} (G : RationalFamily X T)

def evaluation (a : ℂ) (τ : T.Carrier) : X.Carrier := G.finite (a,τ)

lemma evaluation_holomorphic (a : ℂ) :
    ContMDiff (ModelWithCorners T) (ModelWithCorners X) ω (G.evaluation a) :=
  G.finite_holomorphic.comp (contMDiff_const.prodMk contMDiff_id)

lemma evaluation_surjective_derivative {τ : T.Carrier}
    (hs : Function.Surjective (mfderiv (ModelWithCorners T)
      ((ModelWithCorners X).prod (ModelWithCorners X)) (G.twoPointEvaluation 0 1) τ)) :
    Function.Surjective (mfderiv (ModelWithCorners T) (ModelWithCorners X) (G.evaluation 1) τ) := by
  intro w
  obtain ⟨v,hv⟩ := hs (0,w)
  refine ⟨v,?_⟩
  rw [G.twoPointEvaluation_derivative] at hv
  exact congrArg Prod.snd hv

lemma evaluation_open
    (hs : ∀τ,Function.Surjective (mfderiv (ModelWithCorners T)
      ((ModelWithCorners X).prod (ModelWithCorners X)) (G.twoPointEvaluation 0 1) τ)) :
    IsOpenMap (G.evaluation 1) :=
  HolomorphicLocalDiffeomorph.isOpenMap_of_surjective_mfderiv (G.evaluation_holomorphic 1)
    (fun τ => G.evaluation_surjective_derivative (hs τ))

end RationalFamily
namespace TangentSplitting
variable {X : ComplexManifold.{u}} [CompactSpace X.Carrier] [ConnectedSpace X.Carrier]
    (S : TangentSplitting X) (e : ProjectiveEmbedding X)

 

omit [ConnectedSpace X.Carrier] in
theorem exists_open_positive_leaves (hRC : RationallyConnected e) (hdim : 0<X.dim) :
    ∃U : Set X.Carrier,IsOpen U ∧ U.Nonempty ∧
      ∀x∈U,∃g : RationalCurve X,g.finite 1=x ∧ g.TangentTo S.first ∧ PointedGenerated g S.first := by
  obtain ⟨T,hT,G,hs⟩ := hRC.exists_submersive_family e hdim
  let := hT
  refine ⟨Set.range (G.evaluation 1),(G.evaluation_open hs).isOpen_range,
    Set.range_nonempty _,?_⟩
  rintro x ⟨τ,rfl⟩
  obtain ⟨B⟩ := S.exists_projective_tangent_box e (G.curve τ)
  exact ⟨B.firstFactor 1,B.firstFactor_diagonal 1,B.firstFactor_tangentTo 1,
    B.firstFactor_pointedGenerated (G.pointedGenerated_of_submersive S τ (hs τ))⟩

 

theorem exists_open_compact_leaves (hRC : RationallyConnected e) (hdim : 2≤X.dim) :
    ∃L : LeafJetAtlas S,∃U : Set X.Carrier,IsOpen U ∧ U.Nonempty ∧
      ∀x∈U,IsCompact (L.leaf x) ∧
        ∀y∈L.leaf x,L.plaques.LocallySinglePlaque (L.leaf x) y := by
  obtain ⟨hI₁,hI₂⟩ := S.integrable_of_rationallyConnected e hRC hdim
  let L := S.leafJetAtlas hI₁ hI₂
  obtain ⟨U,hU,hUn,hg⟩ := S.exists_open_positive_leaves e hRC (by omega)
  refine ⟨L,U,hU,hUn,?_⟩
  intro x hx
  obtain ⟨g,he,ht,hp⟩ := hg x hx
  obtain ⟨F⟩ := g.exists_frames e
  rw [←he]
  exact ⟨F.leaf_isCompact L ht hp,F.leaf_locallySinglePlaque L ht hp⟩

end TangentSplitting
end SplitTangent

end

end OAI
