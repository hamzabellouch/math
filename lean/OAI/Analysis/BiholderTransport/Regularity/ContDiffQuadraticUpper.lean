import Mathlib

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

namespace WeakMTWTransport

lemma contDiffAt_quadratic_upper {f : ℝ → ℝ} (hf : ContDiffAt ℝ 2 f 0)
    (hf0 : f 0=0) (hd0 : deriv f 0=0) :
    ∃ eps C : ℝ, 0<eps ∧ 0<C ∧ ∀ s ∈ Ioo 0 eps, f s≤C*s^2 := by
  obtain ⟨K,U,hU,hLip⟩ := (hf.derivWithin (m := 1) (by norm_num)).exists_lipschitzOnWith
  have hnear : ∀ᶠ s : ℝ in 𝓝 0, DifferentiableAt ℝ f s :=
    (hf.eventually (by norm_num)).mono (fun _ h => h.differentiableAt (by norm_num))
  obtain ⟨eps,heps,hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hU hnear)
  refine ⟨eps,(K:ℝ)+1,heps,by positivity,?_⟩
  intro s hs
  have hsub : Icc 0 s ⊆ Metric.ball (0:ℝ) eps := by
    intro r hr
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg hr.1] using hr.2.trans_lt hs.2
  have hzero : (0:ℝ) ∈ U := (hball (Metric.mem_ball_self heps)).1
  have hbound : ∀ r ∈ Icc 0 s, ‖deriv f r‖ ≤ (K:ℝ)*s := by
    intro r hr
    have H := hLip.dist_le_mul r (hball (hsub hr)).1 0 hzero
    have H' : ‖deriv f r‖ ≤ (K:ℝ)*r := by
      simpa only [hd0,dist_zero_right,Real.norm_eq_abs,abs_of_nonneg hr.1] using H
    exact H'.trans (mul_le_mul_of_nonneg_left hr.2 K.coe_nonneg)
  have H := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun r hr => (hball (hsub hr)).2) hbound (convex_Icc (0:ℝ) s)
    (left_mem_Icc.mpr hs.1.le) (right_mem_Icc.mpr hs.1.le)
  have H' : |f s|≤(K:ℝ)*s^2 := by
    simpa only [hf0,sub_zero,Real.norm_eq_abs,abs_of_pos hs.1,pow_two,mul_assoc] using H
  exact (le_abs_self (f s)).trans (H'.trans (by nlinarith [sq_nonneg s]))

end WeakMTWTransport

end

end OAI
