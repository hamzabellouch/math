import Mathlib
import OAI.Geometry.SplitTangent.FoliationLeaves
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.PositiveTangentCurves
import OAI.Geometry.SplitTangent.RationalCurveFrames
import OAI.Geometry.SplitTangent.LeafPlaques
import OAI.Geometry.SplitTangent.ProjectiveLinearCoordinates
import OAI.Geometry.SplitTangent.LeafRank
import OAI.Geometry.SplitTangent.LeafAffineRelations
import OAI.Geometry.SplitTangent.RationalVariation

namespace OAI

/-! Compact Positive Leaf. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
universe u
namespace SplitTangent.RationalCurveFrames
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  {e : ProjectiveEmbedding X} {g : RationalCurve X} (F : RationalCurveFrames e g)
  (L : LeafJetAtlas S) [PreconnectedSpace X.Carrier]

include F in
lemma closure_locallySinglePlaque (ht : g.TangentTo S.first)
    (hg : PointedGenerated g S.first) {z : X.Carrier}
    (hz : z∈closure (L.leaf (g.finite 1))) :
    L.plaques.LocallySinglePlaque (closure (L.leaf (g.finite 1))) z := by
  classical
  let P := L.chart z
  let x := P.chart z
  have hzs : z∈P.chart.source := L.mem_source z
  have hxt : x∈P.chart.target := P.chart.map_source hzs
  obtain ⟨i,hi⟩ := Function.ne_iff.mp (e.map z).rep_nonzero
  have hi' : (e.map (P.chart.symm x)).rep i≠0 := by
    simpa only [x,P.chart.left_inv hzs,Pi.zero_apply] using hi
  let patch := {y : X.Carrier | (e.map y).rep i≠0}
  have hpatch : P.chart.symm ⁻¹' patch∈𝓝 x :=
    (P.chart.symm.continuousAt hxt).preimage_mem_nhds ((e.open_patch i).mem_nhds hi')
  obtain ⟨U,V,hU,hUc,hV,hx,hrect⟩ := UniformPlaqueSlices.connected_rectangle
    (Filter.inter_mem (P.chart.open_target.mem_nhds hxt) hpatch)
  have hrectT : U ×ˢ V⊆P.chart.target := fun t hh => (hrect hh).1
  have hrectP : ∀t∈U ×ˢ V,(e.map (P.chart.symm t)).rep i≠0 := fun t hh => (hrect hh).2
  obtain ⟨p,Q,hxQ,hQ,_,_⟩ := e.exists_linear_plaque_coordinates P hxt i hi'
  have hsecond : ∀t,(Q t).2=t.2 := by
    intro t
    rw [hQ]
  obtain ⟨U',V',hU',hUc',hV',hxU',hxV',hVV,hQT,hslice⟩ :=
    UniformPlaqueSlices.exists_slices Q hxQ hsecond hU hV hx
  let T : Set (S.SecondModel z) := {b | b∈V' ∧ ∃a∈U,P.chart.symm (a,b)∈closure (L.leaf (g.finite 1))}
  have hbase : x.2∈T := by
    refine ⟨hxV',x.1,hx.1,?_⟩
    simpa only [Prod.mk.eta,x,P.chart.left_inv hzs] using hz
  let lift : S.FirstModel z → S.SecondModel z → X.Carrier := fun a b => P.chart.symm (Q.symm (a,b))
  have hliftUV : ∀a∈U',∀b∈T,Q.symm (a,b)∈U ×ˢ V :=
    fun a ha b hb => (hslice a ha b hb.1).1
  have hliftP : ∀a∈U',∀b∈T,(e.map (lift a b)).rep i≠0 :=
    fun a ha b hb => hrectP _ (hliftUV a ha b hb)
  have hliftW : ∀a∈U',∀b∈T,lift a b∈closure (L.leaf (g.finite 1)) := by
    intro a ha b hb
    obtain ⟨a₀,ha₀,hw⟩ := hb.2
    have hs := hslice a ha b hb.1
    have hh := L.plaques.closure_saturated hU hUc hV hrectT ha₀ hs.1.1 (hVV hb.1) hw
    change P.chart.symm _∈closure (L.leaf (g.finite 1))
    have he : ((Q.symm (a,b)).1,b)=Q.symm (a,b) := by
      exact Prod.ext rfl hs.2.symm
    rwa [he] at hh
  let r := Module.finrank ℂ (S.first (g.finite 1))
  have hr : Module.finrank ℂ (S.FirstModel z)=Module.finrank ℂ (Fin r → ℂ) := by
    rw [←P.first_finrank hzs]
    simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin,r] using
      L.first_rank_eq z (g.finite 1)
  let E : S.FirstModel z ≃L[ℂ] (Fin r → ℂ) := ContinuousLinearEquiv.ofFinrankEq hr
  let coord : X.Carrier → Fin (e.N+1) → ℂ := fun y => projectiveCoordinates i (e.map y)
  let first : X.Carrier → Fin r → ℂ := fun y => E (p (coord y))
  have hfirst : ∀a∈U',∀b∈T,first (lift a b)=E a := by
    intro a ha b hb
    have hh := congrArg Prod.fst (Q.right_inv (hQT (show (a,b)∈U' ×ˢ V' from ⟨ha,hb.1⟩)))
    rw [hQ] at hh
    exact congrArg E hh
  have hinj : ∀a∈U',InjOn (fun b => coord (lift a b)) T := by
    intro a ha b hb c hc he
    have he' := e.coordinates_injOn i (hliftP a ha b hb) (hliftP a ha c hc) he
    have hP₁ := P.chart.right_inv (hrectT (hliftUV a ha b hb))
    have hP₂ := P.chart.right_inv (hrectT (hliftUV a ha c hc))
    have hh := congrArg (fun y => (P.chart y).2) he'
    change (P.chart (P.chart.symm (Q.symm (a,b)))).2=
      (P.chart (P.chart.symm (Q.symm (a,c)))).2 at hh
    rw [hP₁,hP₂,(hslice a ha b hb.1).2,(hslice a ha c hc.1).2] at hh
    exact hh
  have hrels := fun j => F.leaf_closure_affine_relation L (L.chart (g.finite 1))
    (L.mem_source _) ht hg (E.toLinearMap.comp p.toLinearMap) i j
  choose q hq hroot using hrels
  have hT : T.Finite := PolynomialSpecialization.finite_transversal T hU' ⟨(Q x).1,hxU'⟩
    E lift coord first hfirst hinj q hq (by
      intro a ha b hb j
      exact hroot j (lift a b) (hliftW a ha b hb) (hliftP a ha b hb))
  apply L.plaques.locallySinglePlaque_of_finite_transversal hU hUc hV'
    (fun t ht => hrectT ⟨ht.1,hVV ht.2⟩) hzs ⟨hx.1,hbase.1⟩ hT
  intro y hy hys hyUV
  refine ⟨hyUV.2,(P.chart y).1,hyUV.1,?_⟩
  change P.chart.symm (P.chart y)∈closure (L.leaf (g.finite 1))
  simpa only [P.chart.left_inv hys] using hy

include F in
theorem leaf_isClosed (ht : g.TangentTo S.first) (hg : PointedGenerated g S.first) :
    IsClosed (L.leaf (g.finite 1)) :=
  L.plaques.leaf_isClosed_of_locallySinglePlaque _ (fun _ hz => F.closure_locallySinglePlaque L ht hg hz)

include F in
theorem leaf_isCompact [CompactSpace X.Carrier]
    (ht : g.TangentTo S.first) (hg : PointedGenerated g S.first) :
    IsCompact (L.leaf (g.finite 1)) := (F.leaf_isClosed L ht hg).isCompact

end SplitTangent.RationalCurveFrames

namespace SplitTangent.TangentSplitting
variable {X : ComplexManifold.{u}} [CompactSpace X.Carrier] [ConnectedSpace X.Carrier]
    (S : TangentSplitting X) (e : ProjectiveEmbedding X)

 

theorem exists_compact_leaf (hRC : RationallyConnected e) (hdim : 2≤X.dim) :
    ∃L : LeafJetAtlas S,∃g : RationalCurve X,
      g.TangentTo S.first ∧ PointedGenerated g S.first ∧
      IsCompact (L.leaf (g.finite 1)) ∧ L.leaf (g.finite 1)≠∅ := by
  obtain ⟨hI₁,hI₂⟩ := S.integrable_of_rationallyConnected e hRC hdim
  let L := S.leafJetAtlas hI₁ hI₂
  obtain ⟨g,ht,hg⟩ := S.exists_positive_tangent_curve e hRC (by omega)
  obtain ⟨F⟩ := g.exists_frames e
  refine ⟨L,g,ht,hg,F.leaf_isCompact L ht hg,?_⟩
  exact Set.nonempty_iff_ne_empty.mp ⟨g.finite 1,PlaqueSystem.Reachable.refl L.plaques _⟩

end SplitTangent.TangentSplitting

end

end OAI
