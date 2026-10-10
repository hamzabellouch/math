import Mathlib
import OAI.Geometry.SplitTangent.LeafJetAtlas
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.SwappedProductChart
import OAI.Geometry.SplitTangent.SmoothLeafQuotient

namespace OAI

/-! Everywhere Smooth Leaf Quotient. -/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
universe u
namespace SplitTangent.LeafJetAtlas
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}
  [CompactSpace X.Carrier] [ConnectedSpace X.Carrier]
  (L : LeafJetAtlas S) (M : LeafJetAtlas S.swap) (e : ProjectiveEmbedding X)
  (hRC : RationallyConnected e) (hdim : 0<X.dim)

lemma exists_quotientChartData_of_pair_injective
    (hinj : Function.Injective (L.leafPair M e hRC hdim)) (x : X.Carrier) :
    ∃ D : L.QuotientChartData e hRC hdim x,
      L.leafQuotient e hRC hdim x∈D.chart.source := by
  let P := L.chart x
  have hxs := L.mem_source x
  have hxt := P.chart.map_source hxs
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (P.chart.open_target.mem_nhds hxt)
  let U := Metric.ball (P.chart x).1 r
  let V := Metric.ball (P.chart x).2 r
  have hrect : U ×ˢ V ⊆ P.chart.target := by
    intro p hp
    apply hsub
    simpa only [U,V,Set.mem_prod,Metric.mem_ball,Prod.dist_eq,max_lt_iff] using hp
  have ha : (P.chart x).1∈U := Metric.mem_ball_self hr
  have hb : (P.chart x).2∈V := Metric.mem_ball_self hr
  have hcol : ∀b∈V,((P.chart x).1,b)∈P.chart.target :=
    fun b hb => hrect (show ((P.chart x).1,b)∈U ×ˢ V from ⟨ha,hb⟩)
  have hi : Set.InjOn (fun b => L.leafQuotient e hRC hdim (P.chart.symm ((P.chart x).1,b))) V := by
    intro b hb c hc he
    have hm : M.leafQuotient e hRC hdim (P.chart.symm ((P.chart x).1,b))=
        M.leafQuotient e hRC hdim (P.chart.symm ((P.chart x).1,c)) := by
      apply (M.leafQuotient_eq_iff e hRC hdim _ _).mpr
      exact M.arbitrary_plaque_mem_leaf P.swap (b := (P.chart x).1)
        (convex_ball _ _).isPreconnected (fun k hk => by
          rw [AlignedProductChart.swap_target]
          exact hcol k hk) hb hc
    have hp := hinj (Prod.ext he hm)
    have hp' := congrArg P.chart hp
    rw [P.chart.right_inv (hcol b hb),P.chart.right_inv (hcol c hc)] at hp'
    exact congrArg Prod.snd hp'
  let D : L.QuotientChartData e hRC hdim x :=
    ⟨U,V,(P.chart x).1,Metric.isOpen_ball,(convex_ball _ _).isPreconnected,
      Metric.isOpen_ball,hrect,ha,hi⟩
  refine ⟨D,?_⟩
  have h := D.quotient_mem_chart_rectangle ha hb
  simpa only [P,Prod.eta,(L.chart x).chart.left_inv hxs] using h

lemma smoothLeafLocus_eq_univ_of_pair_injective
    (hinj : Function.Injective (L.leafPair M e hRC hdim)) :
    L.smoothLeafLocus e hRC hdim=univ := by
  apply Set.eq_univ_of_forall
  intro q
  obtain ⟨x,rfl⟩ := L.surjective_leafQuotient e hRC hdim q
  obtain ⟨D,hD⟩ := L.exists_quotientChartData_of_pair_injective M e hRC hdim hinj x
  exact ⟨x,D,hD⟩

end SplitTangent.LeafJetAtlas

end

end OAI
