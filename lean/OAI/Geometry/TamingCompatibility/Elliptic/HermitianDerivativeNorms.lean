import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.RadialNorm
import OAI.Geometry.TamingCompatibility.Functional.HermitianRadialProfiles

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter ContinuousAlternatingMap
open scoped ContDiff Topology RealInnerProductSpace
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma linear_pullback_fderiv_norm (L : E →L[ℝ] F) {f : F → ℝ}
    (hf : ContDiff ℝ ∞ f) (z : E) :
    ‖fderiv ℝ (fun x => f (L x)) z‖ ≤ ‖fderiv ℝ f (L z)‖ * ‖L‖ := by
  rw [fderiv_fun_comp z (hf.differentiable (by simp) _) L.differentiableAt,L.fderiv]
  exact ContinuousLinearMap.opNorm_comp_le _ _

lemma linear_pullback_hessian_norm (L : E →L[ℝ] F) {f : F → ℝ}
    (hf : ContDiff ℝ ∞ f) (z : E) :
    ‖fderiv ℝ (fderiv ℝ (fun x => f (L x))) z‖ ≤
      ‖fderiv ℝ (fderiv ℝ f) (L z)‖ * ‖L‖^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [linear_pullback_hessian L hf]
  have h := (fderiv ℝ (fderiv ℝ f) (L z)).le_opNorm₂ (L u) (L v)
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ f) (L z)‖ * ‖L u‖ * ‖L v‖ := h
    _ ≤ ‖fderiv ℝ (fderiv ℝ f) (L z)‖ * (‖L‖ * ‖u‖) * (‖L‖ * ‖v‖) := by
      gcongr <;> exact L.le_opNorm _
    _ = _ := by ring

lemma hermitianGraph_norm_ge (K : E →L[ℝ] E) (z : E) : ‖z‖ ≤ ‖hermitianGraph K z‖ := by
  have h := hermitianGraph_norm_sq K z
  nlinarith [sq_nonneg ‖K z‖,norm_nonneg (hermitianGraph K z),norm_nonneg z]

lemma norm_hermitianGraph_le (K : E →L[ℝ] E) : ‖hermitianGraph K‖ ≤ 1+‖K‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  have hn : ‖hermitianGraph K z‖ ≤ ‖z‖ + ‖K z‖ := by
    have h1 := hermitianGraph_norm_sq K z
    have hpos := mul_nonneg (norm_nonneg z) (norm_nonneg (K z))
    nlinarith only [h1,norm_nonneg (hermitianGraph K z),norm_nonneg z,
      norm_nonneg (K z),hpos]
  calc
    _ ≤ ‖z‖ + ‖K z‖ := hn
    _ ≤ ‖z‖ + ‖K‖ * ‖z‖ := add_le_add_right (K.le_opNorm z) _
    _ = _ := by ring

lemma norm_hermitianLog_gradient (K : E →L[ℝ] E) {s : ℝ} (hs : 0 < s) (z : E) :
    ‖fderiv ℝ (hermitianLogPotential K s) z‖ ≤ 2*(1+‖K‖)/(s+‖z‖) := by
  calc
    _ ≤ ‖fderiv ℝ (logPotential s) (hermitianGraph K z)‖ * ‖hermitianGraph K‖ :=
      linear_pullback_fderiv_norm _ (logPotential_smooth hs) z
    _ ≤ (2/(s+‖hermitianGraph K z‖)) * (1+‖K‖) := by
      gcongr
      exact norm_logPotential_fderiv hs _
      exact norm_hermitianGraph_le K
    _ ≤ (2/(s+‖z‖)) * (1+‖K‖) := by
      gcongr
      exact hermitianGraph_norm_ge K z
    _ = _ := by ring

lemma norm_hermitianLog_hessian (K : E →L[ℝ] E) {s : ℝ} (hs : 0 < s) (z : E) :
    ‖fderiv ℝ (fderiv ℝ (hermitianLogPotential K s)) z‖ ≤ 6*(1+‖K‖)^2/(s+‖z‖)^2 := by
  let : NormedAddCommGroup (WithLp 2 (E × E)) := inferInstance
  let : NormedSpace ℝ (WithLp 2 (E × E)) := inferInstance
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ (logPotential s)) (hermitianGraph K z)‖ * ‖hermitianGraph K‖^2 :=
      linear_pullback_hessian_norm _ (logPotential_smooth hs) z
    _ ≤ (6/(s+‖hermitianGraph K z‖)^2) * (1+‖K‖)^2 := by
      gcongr
      exact norm_logPotential_hessian hs _
      exact norm_hermitianGraph_le K
    _ ≤ (6/(s+‖z‖)^2) * (1+‖K‖)^2 := by
      gcongr
      exact hermitianGraph_norm_ge K z
    _ = _ := by ring

lemma norm_hermitianSqrt_gradient (K : E →L[ℝ] E) {s : ℝ} (hs : 0 < s) (z : E) :
    ‖fderiv ℝ (hermitianSqrtPotential K s) z‖ ≤ 1+‖K‖ := by
  calc
    _ ≤ ‖fderiv ℝ (sqrtPotential s) (hermitianGraph K z)‖ * ‖hermitianGraph K‖ :=
      linear_pullback_fderiv_norm _ (sqrtPotential_smooth hs) z
    _ ≤ 1 * (1+‖K‖) := by
      gcongr
      exact norm_sqrtPotential_fderiv hs _
      exact norm_hermitianGraph_le K
    _ = _ := one_mul _

lemma norm_hermitianSqrt_hessian (K : E →L[ℝ] E) {s : ℝ} (hs : 0 < s) (z : E) :
    ‖fderiv ℝ (fderiv ℝ (hermitianSqrtPotential K s)) z‖ ≤ 4*(1+‖K‖)^2/(s+‖z‖) := by
  let : NormedAddCommGroup (WithLp 2 (E × E)) := inferInstance
  let : NormedSpace ℝ (WithLp 2 (E × E)) := inferInstance
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ (sqrtPotential s)) (hermitianGraph K z)‖ * ‖hermitianGraph K‖^2 :=
      linear_pullback_hessian_norm _ (sqrtPotential_smooth hs) z
    _ ≤ (4/(s+‖hermitianGraph K z‖)) * (1+‖K‖)^2 := by
      gcongr
      exact norm_sqrtPotential_hessian hs _
      exact norm_hermitianGraph_le K
    _ ≤ (4/(s+‖z‖)) * (1+‖K‖)^2 := by
      gcongr
      exact hermitianGraph_norm_ge K z
    _ = _ := by ring
end TamingCompatibility.RadialPotential

end

end OAI
