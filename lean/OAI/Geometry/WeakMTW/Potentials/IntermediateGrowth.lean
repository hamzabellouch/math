import Mathlib
import OAI.Geometry.WeakMTW.Potentials.IntermediateDefinitions
import OAI.Geometry.WeakMTW.Potentials.IntermediateGrowthMetric

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
open QuadraticEnvelope RiemannianLocal ChartMetric

 theorem growthGap_uniform {a b : ℝ} (ha : 0 < a) (_hab : a ≤ b) (hb : b < 1) :
     ∃ r κ : ℝ, 0 < r ∧ 0 < κ ∧ ∀ t ∈ Icc a b,
       ∀ q ∈ totalMinimizingSet (n := n) (M := M), ∀ x : M, dist q.1 x < r →
         κ*(dist q.1 x)^2 ≤ growthGap (t,q) x-growthGap (t,q) q.1 := by
   classical
   let K := Icc a b ×ˢ totalMinimizingSet (n := n) (M := M)
   have hK : IsCompact K := isCompact_Icc.prod totalMinimizingSet_compact
   choose U hU haU r κ hr hκ hg using (fun α : K => growthGap_local_metric
     (ha.trans_le α.property.1.1) (α.property.1.2.trans_lt hb) α.property.2)
   obtain ⟨L,hL⟩ := hK.elim_finite_subcover U hU (fun α hα => mem_iUnion.mpr ⟨⟨α,hα⟩,haU ⟨α,hα⟩⟩)
   have hnb : (⋂ i ∈ L, Iio (min (r i) (κ i))) ∈ 𝓝 (0:ℝ) :=
     (Filter.biInter_mem L.finite_toSet).mpr (fun i _ => Iio_mem_nhds (lt_min (hr i) (hκ i)))
   obtain ⟨ε,hε,hεb⟩ := Metric.mem_nhds_iff.mp hnb
   have hεmem : ε/2 ∈ Metric.ball (0:ℝ) ε := by
     simp only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos (half_pos hε)]
     linarith
   have hsmall (i : K) (hi : i ∈ L) : ε/2 < r i ∧ ε/2 < κ i :=
     lt_min_iff.mp (mem_iInter₂.mp (hεb hεmem) i hi)
   refine ⟨ε/2,ε/2,half_pos hε,half_pos hε,?_⟩
   intro t ht q hq x hx
   obtain ⟨i,hi,hαU⟩ := mem_iUnion₂.mp (hL (show (t,q) ∈ K from ⟨ht,hq⟩))
   exact (mul_le_mul_of_nonneg_right (hsmall i hi).2.le (sq_nonneg _)).trans
     (hg i (t,q) hαU (ha.trans_le ht.1) (ht.2.trans_lt hb) hq x (hx.trans (hsmall i hi).1))

 theorem intermediate_uniform_growth (hMTW : HasWeakMTW (n := n) (M := M)) :
     UniformIntermediateGrowth (n := n) (M := M) := by
   intro a b ha hab hb
   obtain ⟨r,κ,hr,hκ,hgap⟩ := growthGap_uniform (n := n) (M := M) ha hab hb
   refine ⟨r,κ,hr,hκ,?_⟩
   intro u hu t ht q x hx
   have ht0 : 0 < t := ha.trans_le ht.1
   have ht1 : t < 1 := ht.2.trans_lt hb
   have hsup := (globalSupportingProperty hMTW hu).1 q.val.1 q.val.2 q.property
   have hg := hgap t ht q.val hsup.1 x hx
   have hs0 : 0 < (1+t)/2 := by linarith
   have hs1 : (1+t)/2 < 1 := by linarith
   have hsplit := shortened_upper_difference hsup.1 hs0 hs1 x
   have hu' := hsup.2 x
   change u q.val.1+cost q.val.1 (exp q.val.1 (t•q.val.2))/t+κ*(dist q.val.1 x)^2 ≤
     u x+cost x (exp q.val.1 (t•q.val.2))/t
   dsimp only [growthGap,intermediateCenter,Prod.fst,Prod.snd] at hg
   rw [sub_div] at hsplit
   linarith
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
