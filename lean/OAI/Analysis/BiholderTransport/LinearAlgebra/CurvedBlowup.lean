import Mathlib
import OAI.Analysis.BiholderTransport.CostGeometry.CurvedQuadratic
import OAI.Analysis.BiholderTransport.Regularity.TrialBlowup

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

open Set Filter
open scoped Topology ContDiff

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped ContDiff Topology

open Filter Set
open scoped Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma conjugate_curved_hessian_upper {x : M} {p e xi k : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ minimizingVectors x)
    (hseg : ∀ᶠ s : ℝ in 𝓝 0, p+s • e ∈ minimizingVectors x)
    (hk : mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) x) 𝓘(ℝ,Model n) (riemannianExp x) p k=0)
    (hpair : inner ℝ k xi≠0) :
    ∃ eps B c : ℝ, 0<eps ∧ 0<c ∧ ∀ s ∈ Ioo 0 eps,
      hessianValue x ((1-s^2) • (p+s • e)) xi ≤ B-c/s^2 := by
  obtain ⟨t,ht,ht1,hleft,hright⟩ := exists_minimizing_two_regular_legs hp
  let V := TangentSpace 𝓘(ℝ,Model n) x
  let Q := splitTrialValue x t 0 k
  let a := splitTrialValue x t xi 0
  have hQ0 : Q p=0 := splitTrialValue_conjugate_null ht ht1 hleft hright hk
  have hQ : ContDiffAt ℝ 2 Q p := (splitTrialValue_contDiffAt hleft hright 0 k).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hlinear : Tendsto (fun s : ℝ => p+s • e) (𝓝 0) (𝓝 p) := by
    simpa only [zero_smul,add_zero] using
      (show ContinuousAt (fun s : ℝ => p+s • e) 0 from by fun_prop).tendsto
  have hQmin : ∀ᶠ s : ℝ in 𝓝 0, 0≤Q (p+s • e) := by
    filter_upwards [hseg,hlinear.eventually (split_regular_legs_eventually hleft hright)] with s hs hh
    exact splitTrialValue_nonneg ht ht1 hs hh.1 hh.2
  obtain ⟨eps,C,heps,hC,hquad⟩ := contDiffAt_curved_quadratic_upper hQ hQ0 hQmin
  let W : ℝ → V := fun s => (1-s^2) • (p+s • e)
  have hW0 : W 0=p := by simp [W]
  have hW : Tendsto W (𝓝 0) (𝓝 p) := by
    simpa only [hW0] using (show ContinuousAt W 0 from by dsimp [W]; fun_prop).tendsto
  have ha : ∀ᶠ s : ℝ in 𝓝 0, a (W s)<a p+1 :=
    ((splitTrialValue_contDiffAt hleft hright xi 0).continuousAt.tendsto.comp hW).eventually_lt_const
      (show a p<a p+1 by linarith)
  have hnear := ha.and (hseg.and (hW.eventually (split_regular_legs_eventually hleft hright)))
  obtain ⟨d,hd,hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨min eps (min d 1),a p+1,(inner ℝ k xi)^2/C,
    lt_min heps (lt_min hd zero_lt_one),div_pos (sq_pos_of_ne_zero hpair) hC,?_⟩
  intro s hs
  have hseps := hs.2.trans_le (min_le_left eps (min d 1))
  have hsd := hs.2.trans_le ((min_le_right eps (min d 1)).trans (min_le_left d 1))
  have hs1 := hs.2.trans_le ((min_le_right eps (min d 1)).trans (min_le_right d 1))
  have hh := hball (show s ∈ Metric.ball (0:ℝ) d by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hs.1] using hsd)
  have hr : 0<1-s^2 := by nlinarith [mul_pos hs.1 (sub_pos.mpr hs1)]
  have hr1 : 1-s^2<1 := by nlinarith [sq_pos_of_pos hs.1]
  have hID : W s ∈ injectivityDomain x := contracted_minimizer_mem_injectivityDomain hh.2.1 hr hr1
  obtain ⟨hpos,hSchur⟩ := splitTrialValue_schur ht ht1 hID hh.2.2.1 hh.2.2.2 hpair
  have hq := hquad s ⟨hs.1,hseps⟩
  have hdiv : (inner ℝ k xi)^2/(C*s^2) ≤ (inner ℝ k xi)^2/Q (W s) :=
    div_le_div_of_nonneg_left (sq_nonneg _) hpos hq
  have hid : (inner ℝ k xi)^2/(C*s^2)=((inner ℝ k xi)^2/C)/s^2 := by rw [div_div]
  rw [hid] at hdiv
  exact hSchur.trans (by change a (W s)-(inner ℝ k xi)^2/Q (W s)≤a p+1-_; linarith [hh.1])
end WeakMTWTransport

end

end OAI
