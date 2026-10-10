import Mathlib
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.PositiveTangentCurves
import OAI.Geometry.SplitTangent.RationalCurveFrames
import OAI.Geometry.SplitTangent.ProjectivePositiveLeaf
import OAI.Geometry.SplitTangent.EmbeddedLeafCharts
import OAI.Geometry.SplitTangent.TangentCurveLeaf
import OAI.Geometry.SplitTangent.EmbeddedRationalCurve
import OAI.Geometry.SplitTangent.CompactPositiveLeaf

namespace OAI

/-! Intrinsic Positive Leaf. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
universe u
namespace SplitTangent.RationalCurveFrames
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  {e : ProjectiveEmbedding X} {g : RationalCurve X} (F : RationalCurveFrames e g)
  (L : LeafJetAtlas S) [PreconnectedSpace X.Carrier] [CompactSpace X.Carrier]

include F in
 

theorem exists_intrinsic_positive_leaf (ht : g.TangentTo S.first) (hg : PointedGenerated g S.first) :
    ∃Y : ComplexManifold.{u}, IsProjective Y ∧ ConnectedSpace Y.Carrier ∧
      Y.dim=Module.finrank ℂ (S.first (g.finite 1)) ∧
      ∃i : Y.Carrier → X.Carrier,
        ContMDiff (ModelWithCorners Y) (ModelWithCorners X) ω i ∧
        Function.Injective i ∧ Set.range i=L.leaf (g.finite 1) ∧
        (∀y,LinearMap.range (mfderiv (ModelWithCorners Y) (ModelWithCorners X) i y).toLinearMap=
          S.first (i y)) ∧
        ∃k : RationalCurve Y,PointedGenerated k (fun _ => ⊤) ∧
          (∀z,i (k.finite z)=g.finite z) ∧ (∀z,i (k.infinity z)=g.infinity z) := by
  let h := F.leaf_locallySinglePlaque L ht hg
  let A := L.embeddedAtlas (g.finite 1) h
  let := A.chartedSpace
  let := A.isManifold
  let hf := L.tangent_rational_curve_finite ht
  let hi := L.tangent_rational_curve_infinity ht
  let k := A.rationalCurve g hf hi
  refine ⟨A.manifold,⟨isCompact_iff_compactSpace.mp (F.leaf_isCompact L ht hg),
    ⟨A.projectiveEmbedding e⟩⟩,isConnected_iff_connectedSpace.mp (L.plaques.leaf_isConnected _),rfl,
    Subtype.val,A.inclusion_holomorphic,Subtype.val_injective,Subtype.range_coe,
    L.embedded_inclusion_tangent _ h,k,?_,fun _ => rfl,fun _ => rfl⟩
  exact A.rationalCurve_pointedGenerated g hf hi S.first hg (L.embedded_inclusion_tangent _ h)

end SplitTangent.RationalCurveFrames

end

end OAI
