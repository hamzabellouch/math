import Mathlib
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.PositiveTangentCurves
import OAI.Geometry.SplitTangent.RationalCurveFrames
import OAI.Geometry.SplitTangent.EmbeddedLeafCharts
import OAI.Geometry.SplitTangent.CompactPositiveLeaf
import OAI.Geometry.SplitTangent.PlaqueTangentImage
import OAI.Geometry.SplitTangent.TangentCurveLeaf

namespace OAI

/-! Projective Positive Leaf. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
universe u
namespace SplitTangent.LeafJetAtlas
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  (L : LeafJetAtlas S) (x₀ : X.Carrier) [PreconnectedSpace X.Carrier]
  (h : ∀y∈L.leaf x₀,L.plaques.LocallySinglePlaque (L.leaf x₀) y)

lemma embedded_inclusion_tangent : let A := L.embeddedAtlas x₀ h;
    letI := A.chartedSpace;
    ∀y : L.leaf x₀,LinearMap.range
      (mfderiv 𝓘(ℂ,Fin (Module.finrank ℂ (S.first x₀)) → ℂ) (ModelWithCorners X)
        (Subtype.val : L.leaf x₀ → X.Carrier) y).toLinearMap=S.first y.val := by
  dsimp only
  let A := L.embeddedAtlas x₀ h
  let := A.chartedSpace
  intro y
  let Y := A.manifold
  let i : Y.Carrier → X.Carrier := Subtype.val
  have hi : ContMDiff (ModelWithCorners Y) (ModelWithCorners X) ω i := A.inclusion_holomorphic
  let D : Model Y →L[ℂ] Tangent X y.val := mfderiv (ModelWithCorners Y) (ModelWithCorners X) i y
  have hsub : LinearMap.range D.toLinearMap ≤ S.first y.val := by
    obtain ⟨j,U,V,hU,_,hV,hrect,hys,hyUV,huniq⟩ := h y.val y.property
    let P := L.chart j
    have hc : ContinuousAt (fun z : Y.Carrier => P.chart z.val) y :=
      (P.chart.continuousAt hys).comp continuousAt_subtype_val
    have hs : ∀ᶠ z : Y.Carrier in 𝓝 y,z.val∈P.chart.source :=
      continuousAt_subtype_val.preimage_mem_nhds (P.chart.open_source.mem_nhds hys)
    have hUV : ∀ᶠ z : Y.Carrier in 𝓝 y,P.chart z.val∈U ×ˢ V :=
      hc.preimage_mem_nhds ((hU.prod hV).mem_nhds hyUV)
    have hplaque : ∀ᶠ z : Y.Carrier in 𝓝 y,(P.chart (i z)).2=(P.chart (i y)).2 := by
      filter_upwards [hs,hUV] with z hzs hzUV
      exact huniq z.val z.property hzs hzUV
    rintro v ⟨w,rfl⟩
    exact P.mfderiv_into_first (hi y) hys hplaque w
  let : FiniteDimensional ℂ (Tangent X y.val) := by
    change FiniteDimensional ℂ (Model X)
    infer_instance
  apply Submodule.eq_of_le_of_finrank_eq hsub
  change Module.finrank ℂ (LinearMap.range
    (mfderiv 𝓘(ℂ,Fin (Module.finrank ℂ (S.first x₀)) → ℂ) (ModelWithCorners X)
      (Subtype.val : L.leaf x₀ → X.Carrier) y).toLinearMap)=Module.finrank ℂ (S.first y.val)
  rw [LinearMap.finrank_range_of_inj (A.inclusion_mfderiv_injective y)]
  change Module.finrank ℂ (Fin (Module.finrank ℂ (S.first x₀)) → ℂ)=Module.finrank ℂ (S.first y.val)
  rw [Module.finrank_fintype_fun_eq_card,Fintype.card_fin]
  exact L.first_rank_eq x₀ y.val

include h in
 

theorem exists_projective_leaf (e : ProjectiveEmbedding X) (hc : IsCompact (L.leaf x₀)) :
    ∃Y : ComplexManifold.{u}, IsProjective Y ∧ ConnectedSpace Y.Carrier ∧
      Y.dim=Module.finrank ℂ (S.first x₀) ∧
      ∃i : Y.Carrier → X.Carrier,
        ContMDiff (ModelWithCorners Y) (ModelWithCorners X) ω i ∧
        Function.Injective i ∧ Set.range i=L.leaf x₀ ∧
        ∀y,LinearMap.range (mfderiv (ModelWithCorners Y) (ModelWithCorners X) i y).toLinearMap=
          S.first (i y) := by
  let A := L.embeddedAtlas x₀ h
  let := A.chartedSpace
  refine ⟨A.manifold,⟨isCompact_iff_compactSpace.mp hc,⟨A.projectiveEmbedding e⟩⟩,
    isConnected_iff_connectedSpace.mp (L.plaques.leaf_isConnected x₀),rfl,
    Subtype.val,A.inclusion_holomorphic,Subtype.val_injective,?_,?_⟩
  · exact Subtype.range_coe
  · exact L.embedded_inclusion_tangent x₀ h

end SplitTangent.LeafJetAtlas
namespace SplitTangent.RationalCurveFrames
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  {e : ProjectiveEmbedding X} {g : RationalCurve X} (F : RationalCurveFrames e g)
  (L : LeafJetAtlas S) [PreconnectedSpace X.Carrier] [CompactSpace X.Carrier]

include F in
omit [CompactSpace X.Carrier] in
lemma leaf_locallySinglePlaque (ht : g.TangentTo S.first) (hg : PointedGenerated g S.first) :
    ∀y∈L.leaf (g.finite 1),L.plaques.LocallySinglePlaque (L.leaf (g.finite 1)) y := by
  intro y hy
  have hh := F.closure_locallySinglePlaque L ht hg (subset_closure hy)
  rwa [(F.leaf_isClosed L ht hg).closure_eq] at hh

include F in
theorem exists_projective_leaf (ht : g.TangentTo S.first) (hg : PointedGenerated g S.first) :
    ∃Y : ComplexManifold.{u}, IsProjective Y ∧ ConnectedSpace Y.Carrier ∧
      Y.dim=Module.finrank ℂ (S.first (g.finite 1)) ∧
      ∃i : Y.Carrier → X.Carrier,
        ContMDiff (ModelWithCorners Y) (ModelWithCorners X) ω i ∧
        Function.Injective i ∧ Set.range i=L.leaf (g.finite 1) ∧
        (∀y,LinearMap.range (mfderiv (ModelWithCorners Y) (ModelWithCorners X) i y).toLinearMap=
          S.first (i y)) ∧
        ∃k : RationalCurve Y,(∀z,i (k.finite z)=g.finite z) ∧ (∀z,i (k.infinity z)=g.infinity z) := by
  let h := F.leaf_locallySinglePlaque L ht hg
  let A := L.embeddedAtlas (g.finite 1) h
  let := A.chartedSpace
  let k : RationalCurve A.manifold := {
    finite := fun z => ⟨g.finite z,L.tangent_rational_curve_finite ht z⟩
    infinity := fun z => ⟨g.infinity z,L.tangent_rational_curve_infinity ht z⟩
    finite_holomorphic := A.holomorphic_lift g.finite_holomorphic (L.tangent_rational_curve_finite ht)
    infinity_holomorphic := A.holomorphic_lift g.infinity_holomorphic (L.tangent_rational_curve_infinity ht)
    overlap := fun z hz => Subtype.ext (g.overlap z hz) }
  refine ⟨A.manifold,⟨isCompact_iff_compactSpace.mp (F.leaf_isCompact L ht hg),
    ⟨A.projectiveEmbedding e⟩⟩,isConnected_iff_connectedSpace.mp (L.plaques.leaf_isConnected _),rfl,
    Subtype.val,A.inclusion_holomorphic,Subtype.val_injective,Subtype.range_coe,
    L.embedded_inclusion_tangent _ h,k,fun _ => rfl,fun _ => rfl⟩

end SplitTangent.RationalCurveFrames

end

end OAI
