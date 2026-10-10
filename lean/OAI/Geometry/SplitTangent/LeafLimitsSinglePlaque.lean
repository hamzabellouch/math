import Mathlib
import OAI.Geometry.SplitTangent.FoliationLeaves
import OAI.Geometry.SplitTangent.PlaqueConnectedSets
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.LeafCompactLimits
import OAI.Geometry.SplitTangent.LeafLimitRelations
import OAI.Geometry.SplitTangent.AllCompactLeaves

namespace OAI

/-! Leaf Limits Single Plaque. -/

noncomputable section
open Set Filter Topology TopologicalSpace
open scoped Manifold ContDiff
universe u
namespace SplitTangent.LeafJetAtlas
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  [CompactSpace X.Carrier] [ConnectedSpace X.Carrier]
  (L : LeafJetAtlas S) (e : ProjectiveEmbedding X)

lemma leafLimits_locallySinglePlaque (hRC : RationallyConnected e) (hdim : 0<X.dim)
    {K : Compacts X.Carrier} (hK : K∈L.leafLimits e hRC hdim)
    (x₀ z : X.Carrier) :
    L.plaques.LocallySinglePlaque ((K : Set X.Carrier)) z := by
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
  let T : Set (S.SecondModel z) := {b | b∈V' ∧ ∃a∈U,P.chart.symm (a,b)∈(K : Set X.Carrier)}
  let lift : S.FirstModel z → S.SecondModel z → X.Carrier := fun a b => P.chart.symm (Q.symm (a,b))
  have hliftUV : ∀a∈U',∀b∈T,Q.symm (a,b)∈U ×ˢ V :=
    fun a ha b hb => (hslice a ha b hb.1).1
  have hliftP : ∀a∈U',∀b∈T,(e.map (lift a b)).rep i≠0 :=
    fun a ha b hb => hrectP _ (hliftUV a ha b hb)
  have hliftW : ∀a∈U',∀b∈T,lift a b∈(K : Set X.Carrier) := by
    intro a ha b hb
    obtain ⟨a₀,ha₀,hw⟩ := hb.2
    have hs := hslice a ha b hb.1
    have hh := L.leafLimits_saturated e hRC hdim hK hU hUc hV hrectT ha₀ hs.1.1 (hVV hb.1) hw
    change P.chart.symm _∈(K : Set X.Carrier)
    have he : ((Q.symm (a,b)).1,b)=Q.symm (a,b) := by
      exact Prod.ext rfl hs.2.symm
    rwa [he] at hh
  let r := Module.finrank ℂ (S.first x₀)
  have hr : Module.finrank ℂ (S.FirstModel z)=Module.finrank ℂ (Fin r → ℂ) := by
    rw [←P.first_finrank hzs]
    simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin,r] using
      L.first_rank_eq z x₀
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
  have hrels := fun j => L.leafLimits_affine_relation e hRC hdim hK x₀ (E.toLinearMap.comp p.toLinearMap) i j
  choose q hq hroot using hrels
  have hT : T.Finite := PolynomialSpecialization.finite_transversal T hU' ⟨(Q x).1,hxU'⟩
    E lift coord first hfirst hinj q hq (by
      intro a ha b hb j
      exact hroot j (lift a b) (hliftW a ha b hb) (hliftP a ha b hb))
  apply L.plaques.locallySinglePlaque_of_finite_transversal hU hUc hV'
    (fun t ht => hrectT ⟨ht.1,hVV ht.2⟩) hzs ⟨hx.1,hxV'⟩ hT
  intro y hy hys hyUV
  refine ⟨hyUV.2,(P.chart y).1,hyUV.1,?_⟩
  change P.chart.symm (P.chart y)∈(K : Set X.Carrier)
  simpa only [P.chart.left_inv hys] using hy

lemma leafLimits_subset_leaf (hRC : RationallyConnected e) (hdim : 0<X.dim)
    {K : Compacts X.Carrier} (hK : K∈L.leafLimits e hRC hdim)
    {x : X.Carrier} (hx : x∈(K : Set X.Carrier)) : (K : Set X.Carrier)⊆L.leaf x :=
  L.plaques.preconnected_subset_leaf (L.leafLimits_preconnected e hRC hdim hK)
    (fun z _ => L.leafLimits_locallySinglePlaque e hRC hdim hK x z) hx

lemma leafLimits_eq_leaf (hRC : RationallyConnected e) (hdim : 0<X.dim)
    {K : Compacts X.Carrier} (hK : K∈L.leafLimits e hRC hdim)
    {x : X.Carrier} (hx : x∈(K : Set X.Carrier)) : (K : Set X.Carrier)=L.leaf x := by
  apply subset_antisymm (L.leafLimits_subset_leaf e hRC hdim hK hx)
  let Y := L.leaf x
  let : PreconnectedSpace Y := isPreconnected_iff_preconnectedSpace.mp (L.plaques.leaf_isConnected x).2
  let W : Set Y := {y | y.val∈(K : Set X.Carrier)}
  have hWc : IsClosed W := K.isCompact.isClosed.preimage continuous_subtype_val
  have hWo : IsOpen W := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    obtain ⟨i,U,V,hU,hUc,hV,hT,hys,hyUV,huniq⟩ :=
      L.all_leaf_locallySinglePlaque e hRC hdim x y.val y.property
    let P := (L.chart i).chart
    have hn : ∀ᶠ z : Y in 𝓝 y,z.val∈P.source ∧ P z.val∈U ×ˢ V :=
      (continuous_subtype_val.tendsto y).eventually
        (Filter.Eventually.and (P.open_source.mem_nhds hys)
          ((P.continuousAt hys).preimage_mem_nhds ((hU.prod hV).mem_nhds hyUV)))
    filter_upwards [hn] with z hz
    have he := huniq z.val z.property hz.1 hz.2
    have hh := L.leafLimits_saturated e hRC hdim hK hU hUc hV hT
      hyUV.1 hz.2.1 hyUV.2 (show P.symm ((P y.val).1,(P y.val).2)∈(K : Set X.Carrier) by
        simpa only [Prod.mk.eta,P.left_inv hys] using (show y.val∈(K : Set X.Carrier) from hy))
    change (P z.val).2=(P y.val).2 at he
    have hze : P.symm ((P z.val).1,(P y.val).2)=z.val := by
      rw [←he]
      exact P.left_inv hz.1
    change P.symm ((P z.val).1,(P y.val).2)∈(K : Set X.Carrier) at hh
    change z.val∈(K : Set X.Carrier)
    rwa [hze] at hh
  have hWu : W=univ := IsClopen.eq_univ ⟨hWc,hWo⟩
    ⟨⟨x,PlaqueSystem.Reachable.refl L.plaques x⟩,hx⟩
  intro z hz
  exact show (⟨z,hz⟩ : Y)∈W from hWu ▸ mem_univ _

end SplitTangent.LeafJetAtlas

end

end OAI
