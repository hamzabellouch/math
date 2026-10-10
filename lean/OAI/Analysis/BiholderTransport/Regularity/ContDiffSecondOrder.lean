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

open Filter Set
open scoped Topology

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

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set Filter
open scoped Topology

open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport
lemma contDiffAt_second_order_remainder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiffAt ℝ 2 f 0) :
    (fun h => f h-f 0-fderiv ℝ f 0 h-fderiv ℝ (fderiv ℝ f) 0 h h/2)
      =o[𝓝 0] (fun h : E => ‖h‖^2) := by
  let D := fderiv ℝ f 0
  let B := fderiv ℝ (fderiv ℝ f) 0
  have hs : ∀ v w, B v w=B w v := fun v w => (hf.isSymmSndFDerivAt (by norm_num)).eq v w
  let R : E → ℝ := fun h => f h-f 0-D h-B h h/2
  let R' : E → E →L[ℝ] ℝ := fun h => fderiv ℝ f h-D-B h
  have hB : HasFDerivAt (fderiv ℝ f) B 0 :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num) |>.hasFDerivAt
  obtain ⟨r,hr,hrdiff⟩ := Metric.mem_nhds_iff.mp ((hf.eventually (by norm_num)).mono fun h hh =>
    hh.differentiableAt (by norm_num))
  have hder : ∀ h ∈ Metric.ball (0:E) r, HasFDerivWithinAt R (R' h) (Metric.ball (0:E) r) h := by
    intro h hh
    have hquad : HasFDerivAt (fun z : E => B z z/2) (B h) h := by
      have H := (B.hasFDerivAt_of_bilinear (hasFDerivAt_id h) (hasFDerivAt_id h)).const_smul (1/2:ℝ)
      have heq : (fun z : E => B z z/2) = ((1/2:ℝ) • fun z : E => B z z) := by ext z; simp only [Pi.smul_apply,smul_eq_mul]; ring
      rw [heq]
      apply H.congr_fderiv
      ext v
      simp only [smul_apply,add_apply,ContinuousLinearMap.precompR_apply,
        ContinuousLinearMap.precompL_apply,ContinuousLinearMap.compL_apply,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply,smul_eq_mul,id_eq]
      rw [hs v h]
      ring
    exact (((hrdiff hh).hasFDerivAt.sub_const (f 0)).sub D.hasFDerivAt |>.sub hquad).hasFDerivWithinAt
  have ho : R' =o[𝓝[Metric.ball (0:E) r] (0:E)] fun h => ‖h-(0:E)‖^1 := by
    simpa only [R',D,B,sub_zero,pow_one] using hB.isLittleO.norm_right.mono nhdsWithin_le_nhds
  have H := (convex_ball (0:E) r).isLittleO_pow_succ (Metric.mem_ball_self hr) hder ho
  rw [nhdsWithin_eq_nhds.mpr (Metric.ball_mem_nhds _ hr)] at H
  simpa only [R,D,B,map_zero,zero_apply,zero_div,sub_self,sub_zero] using H
end WeakMTWTransport

end

end OAI
