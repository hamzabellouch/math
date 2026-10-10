import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.MetricDefinitions
import OAI.Analysis.BiholderTransport.LinearAlgebra.ActualRadial
import OAI.Analysis.BiholderTransport.Coordinates.SplitAction
import OAI.Analysis.BiholderTransport.Regularity.SecondScaled
import OAI.Analysis.BiholderTransport.CostGeometry.BranchCost2
import OAI.Analysis.BiholderTransport.Coordinates.ProperPieces

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section Crossing
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))
end Crossing
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section MiddleHessian
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

omit [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma reverseRay_prefix (z : TangentBundle 𝓘(ℝ,Model n) M) (h : ℝ) :
    reverseRay (tangentScale h z)=tangentScale (-h) (sprayFlow h z) := by
  rw [reverseRay,sprayFlow_scale,mul_one,tangentScale_mul,neg_one_mul]

lemma proper_prefix_reverse_in_injectivityDomain {z : TangentBundle 𝓘(ℝ,Model n) M}
    (hz : z.2∈minimizingVectors z.1) {h : ℝ} (hh : 0<h) (hh1 : h<1) :
    (-h) • (sprayFlow h z).2∈injectivityDomain (sprayFlow h z).1 := by
  have H := reverseRay_injectivityDomain (z := tangentScale h z)
    (contracted_minimizer_mem_injectivityDomain hz hh hh1)
  rw [reverseRay_prefix] at H
  exact H

lemma proper_prefix_reverse_endpoint (z : TangentBundle 𝓘(ℝ,Model n) M) (h : ℝ) :
    riemannianExp (sprayFlow h z).1 ((-h) • (sprayFlow h z).2)=z.1 := by
  have H := reverseRay_endpoint (tangentScale h z)
  rw [reverseRay_prefix] at H
  exact H

def middleHessian (z : TangentBundle 𝓘(ℝ,Model n) M) (h T : ℝ) :
    TangentSpace 𝓘(ℝ,Model n) (sprayFlow h z).1 →L[ℝ]
      TangentSpace 𝓘(ℝ,Model n) (sprayFlow h z).1 →L[ℝ] ℝ :=
  h⁻¹ • normalHessian (sprayFlow h z).1 ((-h) • (sprayFlow h z).2)+
    (T-h)⁻¹ • normalHessian (sprayFlow h z).1 ((T-h) • (sprayFlow h z).2)

omit [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma middleHessian_apply (z : TangentBundle 𝓘(ℝ,Model n) M) (h T : ℝ)
    (v w : TangentSpace 𝓘(ℝ,Model n) (sprayFlow h z).1) :
    middleHessian z h T v w=
      normalHessian (sprayFlow h z).1 ((-h) • (sprayFlow h z).2) v w/h+
      normalHessian (sprayFlow h z).1 ((T-h) • (sprayFlow h z).2) v w/(T-h) := by
  simp only [middleHessian,add_apply,smul_apply,
    smul_eq_mul,div_eq_mul_inv]
  ring

def middleCenteredAction (z : TangentBundle 𝓘(ℝ,Model n) M) (h : ℝ)
    (b : TangentSpace 𝓘(ℝ,Model n) (sprayFlow h z).1) : ℝ :=
  h⁻¹*(normalCost (sprayFlow h z).1 ((-h) • (sprayFlow h z).2) b-
    normalCost (sprayFlow h z).1 ((-h) • (sprayFlow h z).2) 0)-
  (-(1-h)⁻¹)*(normalCost (sprayFlow h z).1 ((1-h) • (sprayFlow h z).2) b-
    normalCost (sprayFlow h z).1 ((1-h) • (sprayFlow h z).2) 0)

lemma middle_normal_prefix (z : TangentBundle 𝓘(ℝ,Model n) M) (h : ℝ)
    (b : TangentSpace 𝓘(ℝ,Model n) (sprayFlow h z).1) :
    normalCost (sprayFlow h z).1 ((-h) • (sprayFlow h z).2) b=
      cost z.1 (riemannianExp (sprayFlow h z).1 b) := by
  unfold normalCost
  rw [proper_prefix_reverse_endpoint,cost_symm]

lemma middle_normal_suffix (z : TangentBundle 𝓘(ℝ,Model n) M) (h : ℝ)
    (b : TangentSpace 𝓘(ℝ,Model n) (sprayFlow h z).1) :
    normalCost (sprayFlow h z).1 ((1-h) • (sprayFlow h z).2) b=
      cost (riemannianExp (sprayFlow h z).1 b) (riemannianExp z.1 z.2) := by
  unfold normalCost
  rw [proper_suffix_endpoint,one_smul]

lemma middle_action_contact {z : TangentBundle 𝓘(ℝ,Model n) M}
    (hz : z.2∈minimizingVectors z.1) {h : ℝ} (hh : 0<h) (hh1 : h<1) :
    normalCost (sprayFlow h z).1 ((-h) • (sprayFlow h z).2) 0/h+
      normalCost (sprayFlow h z).1 ((1-h) • (sprayFlow h z).2) 0/(1-h)=
      cost z.1 (riemannianExp z.1 z.2) := by
  rw [middle_normal_prefix,middle_normal_suffix,riemannianExp_zero]
  have H := splitNormalAction_contact hz hh hh1
  simp only [splitNormalAction,normalCost,riemannianExp_zero] at H
  simpa only [riemannianExp_smul] using H

lemma middleCenteredAction_minimum {z : TangentBundle 𝓘(ℝ,Model n) M}
    (hz : z.2∈minimizingVectors z.1) {h : ℝ} (hh : 0<h) (hh1 : h<1) :
    IsLocalMin (middleCenteredAction z h) 0 := by
  filter_upwards [] with b
  have H := squared_dist_divided_action_le z.1 (riemannianExp (sprayFlow h z).1 b)
    (riemannianExp z.1 z.2) hh hh1
  have H' : cost z.1 (riemannianExp z.1 z.2)≤
      normalCost (sprayFlow h z).1 ((-h) • (sprayFlow h z).2) b/h+
      normalCost (sprayFlow h z).1 ((1-h) • (sprayFlow h z).2) b/(1-h) := by
    rw [middle_normal_prefix,middle_normal_suffix]
    convert H using 1 <;> simp only [cost,div_div,mul_comm]
  rw [←middle_action_contact hz hh hh1] at H'
  dsimp only [middleCenteredAction]
  simp only [sub_self,mul_zero,neg_mul,sub_neg_eq_add,div_eq_mul_inv] at H' ⊢
  nlinarith

lemma middleCenteredAction_contDiffAt {z : TangentBundle 𝓘(ℝ,Model n) M}
    (hz : z.2∈minimizingVectors z.1) {h : ℝ} (hh : 0<h) (hh1 : h<1) :
    ContDiffAt ℝ 2 (middleCenteredAction z h) 0 := by
  have hf : ContDiffAt ℝ 2 (normalCost (sprayFlow h z).1 ((-h) • (sprayFlow h z).2)) 0 :=
    (normalCost_contDiffAt (proper_prefix_reverse_in_injectivityDomain hz hh hh1)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hg : ContDiffAt ℝ 2 (normalCost (sprayFlow h z).1 ((1-h) • (sprayFlow h z).2)) 0 :=
    (normalCost_contDiffAt (proper_suffix_in_injectivityDomain hz hh hh1 le_rfl)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  exact (contDiffAt_const.mul (hf.sub contDiffAt_const)).sub
      (contDiffAt_const.mul (hg.sub contDiffAt_const))

lemma middleCenteredAction_hessian {z : TangentBundle 𝓘(ℝ,Model n) M}
    (hz : z.2∈minimizingVectors z.1) {h : ℝ} (hh : 0<h) (hh1 : h<1)
    (v : TangentSpace 𝓘(ℝ,Model n) (sprayFlow h z).1) :
    fderiv ℝ (fderiv ℝ (middleCenteredAction z h)) 0 v v=middleHessian z h 1 v v := by
  have hf : ContDiffAt ℝ 2 (normalCost (sprayFlow h z).1 ((-h) • (sprayFlow h z).2)) 0 :=
    (normalCost_contDiffAt (proper_prefix_reverse_in_injectivityDomain hz hh hh1)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hg : ContDiffAt ℝ 2 (normalCost (sprayFlow h z).1 ((1-h) • (sprayFlow h z).2)) 0 :=
    (normalCost_contDiffAt (proper_suffix_in_injectivityDomain hz hh hh1 le_rfl)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  unfold middleCenteredAction
  rw [second_fderiv_scaled_differences hf hg,middleHessian_apply]
  simp only [normalHessian,neg_mul,sub_neg_eq_add,div_eq_mul_inv,mul_comm]

lemma middleHessian_one_nonneg {z : TangentBundle 𝓘(ℝ,Model n) M}
    (hz : z.2∈minimizingVectors z.1) {h : ℝ} (hh : 0<h) (hh1 : h<1)
    (v : TangentSpace 𝓘(ℝ,Model n) (sprayFlow h z).1) :
    0 ≤ middleHessian z h 1 v v := by
  rw [←middleCenteredAction_hessian hz hh hh1]
  exact localMin_hessian_nonneg (middleCenteredAction_contDiffAt hz hh hh1)
    (middleCenteredAction_minimum hz hh hh1) v

end MiddleHessian
end WeakMTWTransport

end

end

end

end OAI
