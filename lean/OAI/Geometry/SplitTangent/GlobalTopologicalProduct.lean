import Mathlib
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.SwappedProductChart
import OAI.Geometry.SplitTangent.CompactLeafQuotient
import OAI.Geometry.SplitTangent.ArbitraryPlaqueLeaves
import OAI.Geometry.SplitTangent.ComplementaryLeafIntersections

namespace OAI

/-! Global Topological Product. -/

noncomputable section
open Set Filter Topology TopologicalSpace
open scoped Manifold ContDiff
universe u
namespace SplitTangent.LeafJetAtlas
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  [CompactSpace X.Carrier] [ConnectedSpace X.Carrier]
  (L : LeafJetAtlas S) (M : LeafJetAtlas S.swap) (e : ProjectiveEmbedding X)
  (hRC : RationallyConnected e) (hdim : 0<X.dim)

def leafPair (x : X.Carrier) :
    L.CompactLeafSpace e hRC hdim × M.CompactLeafSpace e hRC hdim :=
  (L.leafQuotient e hRC hdim x,M.leafQuotient e hRC hdim x)

lemma continuous_leafPair : Continuous (L.leafPair M e hRC hdim) :=
  (L.continuous_leafQuotient e hRC hdim).prodMk (M.continuous_leafQuotient e hRC hdim)

lemma leafPair_rectangle_image
    {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    (P : AlignedProductChart S A B) {U : Set A} {V : Set B}
    (hUc : IsPreconnected U) (hVc : IsPreconnected V)
    (hrect : U ×ˢ V ⊆ P.chart.target) :
    L.leafPair M e hRC hdim '' (P.chart.symm '' (U ×ˢ V))=
      (L.leafQuotient e hRC hdim '' (P.chart.symm '' (U ×ˢ V))) ×ˢ
      (M.leafQuotient e hRC hdim '' (P.chart.symm '' (U ×ˢ V))) := by
  ext t
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨⟨x,hx,rfl⟩,⟨x,hx,rfl⟩⟩
  · rintro ⟨⟨x,⟨⟨a,b⟩,⟨ha,hb⟩,rfl⟩,hx⟩,⟨y,⟨⟨c,d⟩,⟨hc,hd⟩,rfl⟩,hy⟩⟩
    refine ⟨P.chart.symm (c,b),⟨(c,b),⟨hc,hb⟩,rfl⟩,Prod.ext ?_ ?_⟩
    · change L.leafQuotient e hRC hdim (P.chart.symm (c,b))=t.1
      rw [←hx]
      apply (L.leafQuotient_eq_iff e hRC hdim _ _).mpr
      exact L.arbitrary_plaque_mem_leaf P hUc (fun k hk => hrect ⟨hk,hb⟩) hc ha
    · change M.leafQuotient e hRC hdim (P.chart.symm (c,b))=t.2
      rw [←hy]
      apply (M.leafQuotient_eq_iff e hRC hdim _ _).mpr
      exact M.arbitrary_plaque_mem_leaf P.swap (b := c) hVc (fun k hk => by
        rw [AlignedProductChart.swap_target]
        change (c,k)∈P.chart.target
        exact hrect ⟨hc,hk⟩) hb hd

lemma leafPair_rectangle_image_open
    {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]
    [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    (P : AlignedProductChart S A B) {U : Set A} {V : Set B}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hV : IsOpen V) (hVc : IsPreconnected V)
    (hrect : U ×ˢ V ⊆ P.chart.target) :
    IsOpen (L.leafPair M e hRC hdim '' (P.chart.symm '' (U ×ˢ V))) := by
  rw [L.leafPair_rectangle_image M e hRC hdim P hUc hVc hrect]
  have hopen := P.chart.symm.isOpen_image_of_subset_source (hU.prod hV) hrect
  exact (L.isOpenMap_leafQuotient e hRC hdim _ hopen).prod
    (M.isOpenMap_leafQuotient e hRC hdim _ hopen)

lemma isOpenMap_leafPair : IsOpenMap (L.leafPair M e hRC hdim) := by
  intro W hW
  apply isOpen_iff_mem_nhds.mpr
  rintro q ⟨x,hx,rfl⟩
  let P := L.chart x
  have hxs := L.mem_source x
  have hxt := P.chart.map_source hxs
  have hN : P.chart.target ∩ P.chart.symm ⁻¹' W∈𝓝 (P.chart x) :=
    Filter.inter_mem (P.chart.open_target.mem_nhds hxt)
      ((P.chart.symm.continuousAt hxt).preimage_mem_nhds (by
        rw [P.chart.left_inv hxs]
        exact hW.mem_nhds hx))
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp hN
  let U := Metric.ball (P.chart x).1 r
  let V := Metric.ball (P.chart x).2 r
  have hrect : U ×ˢ V ⊆ P.chart.target ∩ P.chart.symm ⁻¹' W := by
    intro p hp
    apply hsub
    simpa only [U,V,Set.mem_prod,Metric.mem_ball,Prod.dist_eq,max_lt_iff] using hp
  have hopen := L.leafPair_rectangle_image_open M e hRC hdim P Metric.isOpen_ball
    (convex_ball _ _).isPreconnected Metric.isOpen_ball (convex_ball _ _).isPreconnected
    (fun p hp => (hrect hp).1)
  have hxin : x∈P.chart.symm '' (U ×ˢ V) :=
    ⟨P.chart x,⟨Metric.mem_ball_self hr,Metric.mem_ball_self hr⟩,P.chart.left_inv hxs⟩
  apply Filter.mem_of_superset (hopen.mem_nhds ⟨x,hxin,rfl⟩)
  rintro q ⟨y,⟨p,hp,rfl⟩,rfl⟩
  exact ⟨P.chart.symm p,(hrect hp).2,rfl⟩

lemma surjective_leafPair : Function.Surjective (L.leafPair M e hRC hdim) := by
  have hc : IsClopen (range (L.leafPair M e hRC hdim)) :=
    ⟨(isCompact_range (L.continuous_leafPair M e hRC hdim)).isClosed,
      by simpa only [Set.image_univ] using L.isOpenMap_leafPair M e hRC hdim Set.univ isOpen_univ⟩
  exact Set.range_eq_univ.mp (hc.eq_univ (Set.range_nonempty _))

lemma leafPair_fiber_eq (x : X.Carrier) :
    {y | L.leafPair M e hRC hdim y=L.leafPair M e hRC hdim x}=L.leaf x ∩ M.leaf x := by
  ext y
  change ((L.leafQuotient e hRC hdim y,M.leafQuotient e hRC hdim y)=
    (L.leafQuotient e hRC hdim x,M.leafQuotient e hRC hdim x)) ↔ _
  rw [Prod.mk.injEq]
  constructor
  · intro h
    exact ⟨(L.leafQuotient_eq_iff e hRC hdim x y).mp h.1.symm,
      (M.leafQuotient_eq_iff e hRC hdim x y).mp h.2.symm⟩
  · intro h
    exact ⟨((L.leafQuotient_eq_iff e hRC hdim x y).mpr h.1).symm,
      ((M.leafQuotient_eq_iff e hRC hdim x y).mpr h.2).symm⟩

lemma leafPair_fiber_finite (q : L.CompactLeafSpace e hRC hdim × M.CompactLeafSpace e hRC hdim) :
    {x | L.leafPair M e hRC hdim x=q}.Finite := by
  obtain ⟨x,rfl⟩ := L.surjective_leafPair M e hRC hdim q
  rw [L.leafPair_fiber_eq M e hRC hdim x]
  exact L.complementary_leaves_finite M e hRC hdim x x

end SplitTangent.LeafJetAtlas

end

end OAI
