import Mathlib
import OAI.Geometry.WeakMTW.Potentials.CovectorFlow
import OAI.Geometry.WeakMTW.Potentials.IntermediateCovectors
import OAI.Geometry.WeakMTW.Potentials.ChartForwardLipschitz

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold NNReal
namespace WeakMTW
noncomputable section
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 structure IntermediateDatum (M : Type*) [MetricSpace M] (a b : ℝ) where
   u : M → ℝ
   v : M → ℝ
   dual : IsDualPair u v
   t : ℝ
   time : t ∈ Icc a b

 def datumInverse (hMTW : HasWeakMTW (n := n) (M := M)) {a b : ℝ}
     (ha : 0 < a) (hb : b < 1) (d : IntermediateDatum M a b) : M → TangentBundle (model n) M :=
   intermediateInverse hMTW ⟨d.v,d.dual.2.1,d.dual.2.2.1⟩ (ha.trans_le d.time.1) (d.time.2.trans_lt hb)

 def datumParameter (z : M) {a b : ℝ} (d : IntermediateDatum M a b) (y : M) : CovectorParameters n :=
   (d.t,chartAt (Model n) z y,
     fderiv ℝ (fun X => hopfLax d.t d.u ((chartAt (Model n) z).symm X)) (chartAt (Model n) z y))

 theorem datumParameter_flow (hMTW : HasWeakMTW (n := n) (M := M)) {a b : ℝ}
     (ha : 0 < a) (hb : b < 1) (z : M) (d : IntermediateDatum M a b) {y : M}
     (hy : y ∈ (chartAt (Model n) z).source) :
     covectorFlow z (datumParameter z d y) = datumInverse hMTW ha hb d y :=
   covectorFlow_eq_inverse hMTW d.dual (ha.trans_le d.time.1) (d.time.2.trans_lt hb) z y hy

 theorem intermediate_parameter_family (hMTW : HasWeakMTW (n := n) (M := M))
     {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) (z : M) :
     ∃ K : Set (CovectorParameters n), IsCompact K ∧
       (∀ A ∈ K, A.2.1 ∈ (chartAt (Model n) z).target) ∧
       ∃ r : ℝ, ∃ C : ℝ≥0, 0 < r ∧ Metric.ball z r ⊆ (chartAt (Model n) z).source ∧
       ∀ d : IntermediateDatum M a b,
         MapsTo (datumParameter (n := n) z d) (Metric.ball z r) K ∧
         LipschitzOnWith C (datumParameter (n := n) z d) (Metric.ball z r) := by
   obtain ⟨R,B,L,hR,_,hT,hbounds⟩ := intermediate_covector_bounds hMTW ha hab hb z
   obtain ⟨S,A,hS,hsrc,hlip⟩ := chart_forward_local_lipschitz (n := n) z
   let c := chartAt (Model n) z
   have hz : z ∈ c.source := mem_chart_source (Model n) z
   have hnear : Metric.ball z S ∩ c ⁻¹' Metric.ball (c z) (R/2) ∈ 𝓝 z :=
     inter_mem (Metric.ball_mem_nhds _ hS)
       ((c.continuousAt hz).preimage_mem_nhds (Metric.ball_mem_nhds _ (half_pos hR)))
   obtain ⟨δ,hδ,hδb⟩ := Metric.mem_nhds_iff.mp hnear
   let K : Set (CovectorParameters n) := Icc a b ×ˢ (Metric.closedBall (c z) (R/2) ×ˢ Metric.closedBall 0 L)
   have hKR : Metric.closedBall (c z) (R/2) ⊆ Metric.ball (c z) R :=
     Metric.closedBall_subset_ball (half_lt_self hR)
   refine ⟨K,isCompact_Icc.prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)),
      fun _ hW => hT (hKR hW.2.1),δ,max 0 (max A (B*A)),hδ,
      fun _ hy => hsrc (hδb hy).1,?_⟩
   intro d
   have hcL : LipschitzOnWith A c (Metric.ball z δ) := hlip.mono (fun _ hy => (hδb hy).1)
   have hcMap : MapsTo c (Metric.ball z δ) (Metric.ball (c z) R) := fun _ hy =>
     Metric.ball_subset_ball (half_le_self hR.le) (hδb hy).2
   have hdL := (hbounds d.u d.v d.dual d.t d.time).1.comp hcL hcMap
   refine ⟨?_,(LipschitzWith.const d.t).lipschitzOnWith.prodMk (hcL.prodMk hdL)⟩
   intro y hy
   refine ⟨d.time,Metric.ball_subset_closedBall (hδb hy).2,?_⟩
   rw [Metric.mem_closedBall,dist_zero_right]
   exact (hbounds d.u d.v d.dual d.t d.time).2 (c y) (hcMap hy)
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
