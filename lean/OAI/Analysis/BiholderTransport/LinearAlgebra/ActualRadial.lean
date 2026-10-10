import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.RadialIdentity

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

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

def normalHessian (x : M) (p : TangentSpace 𝓘(ℝ,Model n) x) :
    TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (normalCost x p)) 0

lemma normalHessian_symm {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ injectivityDomain x) (v w : TangentSpace 𝓘(ℝ,Model n) x) :
    normalHessian x p v w = normalHessian x p w v :=
  ((normalCost_contDiffAt hp).isSymmSndFDerivAt (by simp)).eq v w

lemma hessianValue_eq_normalHessian {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ injectivityDomain x) (v : TangentSpace 𝓘(ℝ,Model n) x) :
    hessianValue x p v=normalHessian x p v v := by
  have H := iteratedDeriv_two_affine_line
    ((normalCost_contDiffAt hp).of_le (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) v
  simpa only [zero_add,normalCost,hessianValue,normalHessian] using H

lemma normalHessian_radial {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p ∈ injectivityDomain x) (v : TangentSpace 𝓘(ℝ,Model n) x) :
    normalHessian x p p v=inner ℝ p v := normalCost_radial_hessian hp v

lemma normalHessian_contracted_radial {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {r : ℝ} (hr : r≠0) (hp : r • p ∈ injectivityDomain x)
    (v : TangentSpace 𝓘(ℝ,Model n) x) : normalHessian x (r • p) p v=inner ℝ p v := by
  have H := normalHessian_radial hp v
  simp only [map_smul,smul_apply,real_inner_smul_left,smul_eq_mul] at H
  exact (mul_left_cancel₀ hr H)

lemma hessianValue_contracted_radial {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    {r : ℝ} (hr : r≠0) (hp : r • p ∈ injectivityDomain x) :
    hessianValue x (r • p) p=‖p‖^2 := by
  rw [hessianValue_eq_normalHessian hp,normalHessian_contracted_radial hr hp,real_inner_self_eq_norm_sq]

lemma hessianValue_transverse_radial_identity {x : M} {p e : TangentSpace 𝓘(ℝ,Model n) x}
    {r s : ℝ} (hr : r≠0) (hp : r • (p+s • e) ∈ injectivityDomain x)
    (hortho : inner ℝ p e=0) :
    hessianValue x (r • (p+s • e)) p = ‖p‖^2+s^2*(hessianValue x (r • (p+s • e)) e-‖e‖^2) := by
  rw [hessianValue_eq_normalHessian hp,hessianValue_eq_normalHessian hp]
  have H1 := normalHessian_contracted_radial hr hp p
  have H2 := normalHessian_contracted_radial hr hp e
  have hep : inner ℝ e p=0 := by rw [real_inner_comm,hortho]
  simp only [map_add,map_smul,add_apply,smul_apply,smul_eq_mul,
    inner_add_left,real_inner_smul_left,hortho,hep,real_inner_self_eq_norm_sq,mul_zero,zero_add,add_zero] at H1 H2
  rw [normalHessian_symm hp e p] at H1
  nlinarith [congrArg (fun a : ℝ => s*a) H2]

end WeakMTWTransport

end

end OAI
