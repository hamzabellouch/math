import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.TwoDirection

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential
open Set Filter ContinuousAlternatingMap
open scoped ContDiff Topology RealInnerProductSpace
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def hermitianGraph (K : E →L[ℝ] E) : E →L[ℝ] WithLp 2 (E × E) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.id ℝ E).prod K)

lemma hermitianGraph_apply (K : E →L[ℝ] E) (z : E) :
    hermitianGraph K z = WithLp.toLp 2 (z,K z) := rfl

lemma hermitianGraph_norm_sq (K : E →L[ℝ] E) (z : E) :
    ‖hermitianGraph K z‖^2 = ‖z‖^2 + ‖K z‖^2 := by
  simp [hermitianGraph_apply,WithLp.prod_norm_sq_eq_of_L2]

lemma hermitianGraph_inner (K : E →L[ℝ] E) (z v : E) :
    ⟪hermitianGraph K z,hermitianGraph K v⟫ = ⟪z,v⟫ + ⟪K z,K v⟫ := rfl

lemma hermitianGraph_complex_pair (K : E →L[ℝ] E) (hK : ∀ v, K (K v) = -v) (v : E) :
    ⟪hermitianGraph K v, hermitianGraph K (K v)⟫ = 0 ∧
      ‖hermitianGraph K (K v)‖ = ‖hermitianGraph K v‖ := by
  constructor
  · rw [hermitianGraph_inner,hK,inner_neg_right,real_inner_comm]
    ring
  · have he : ‖hermitianGraph K (K v)‖^2 = ‖hermitianGraph K v‖^2 := by
      rw [hermitianGraph_norm_sq,hermitianGraph_norm_sq,hK,norm_neg]
      ring
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he

lemma linear_pullback_hessian (L : E →L[ℝ] F) {f : F → ℝ}
    (hf : ContDiff ℝ ∞ f) (z u v : E) :
    fderiv ℝ (fderiv ℝ (fun x => f (L x))) z u v =
      fderiv ℝ (fderiv ℝ f) (L z) (L u) (L v) := by
  have he : fderiv ℝ (fun x => f (L x)) = fun x => (fderiv ℝ f (L x)).comp L := by
    funext x
    simpa only [L.fderiv] using fderiv_fun_comp x (hf.differentiable (by simp) _) L.differentiableAt
  have hf' := (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have hd := ((hf' (L z)).hasFDerivAt.comp z L.hasFDerivAt).clm_comp (hasFDerivAt_const L z)
  dsimp only [Function.comp_def] at hd
  rw [he,hd.fderiv]
  simp

def hermitianLogPotential (K : E →L[ℝ] E) (s : ℝ) (z : E) : ℝ :=
  logPotential s (hermitianGraph K z)

def hermitianSqrtPotential (K : E →L[ℝ] E) (s : ℝ) (z : E) : ℝ :=
  sqrtPotential s (hermitianGraph K z)

lemma hermitianLogPotential_smooth (K : E →L[ℝ] E) {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ ∞ (hermitianLogPotential K s) :=
  (logPotential_smooth hs).comp (hermitianGraph K).contDiff

lemma hermitianSqrtPotential_smooth (K : E →L[ℝ] E) {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ ∞ (hermitianSqrtPotential K s) :=
  (sqrtPotential_smooth hs).comp (hermitianGraph K).contDiff

lemma hermitianLog_ddc_lower (K : E →L[ℝ] E) (hK : ∀ v, K (K v) = -v)
    {s : ℝ} (hs : 0 < s) (z v : E) :
    2*s^2*(‖v‖^2+‖K v‖^2)/(s^2+‖z‖^2+‖K z‖^2)^2 ≤
      extDeriv (ExteriorForms.dc (fun _ => K) (hermitianLogPotential K s)) z ![v,K v] := by
  have hc := hermitianLogPotential_smooth K hs
  have hd : DifferentiableAt ℝ (fderiv ℝ (hermitianLogPotential K s)) z :=
    (hc.fderiv_right (m := ∞) (by simp)).differentiable (by simp) z
  rw [constant_ddc_trace K hK hd]
  change _ ≤ fderiv ℝ (fderiv ℝ (fun x => logPotential s (hermitianGraph K x))) z v v +
    fderiv ℝ (fderiv ℝ (fun x => logPotential s (hermitianGraph K x))) z (K v) (K v)
  rw [linear_pullback_hessian _ (logPotential_smooth hs),
    linear_pullback_hessian _ (logPotential_smooth hs)]
  obtain ⟨ho,hn⟩ := hermitianGraph_complex_pair K hK v
  have h := logPotential_trace_lower hs (hermitianGraph K z)
    (hermitianGraph K v) (hermitianGraph K (K v)) ho hn
  simpa only [hermitianGraph_norm_sq,add_assoc] using h

lemma hermitianSqrt_ddc_lower (K : E →L[ℝ] E) (hK : ∀ v, K (K v) = -v)
    {s : ℝ} (hs : 0 < s) (z v : E) :
    (‖v‖^2+‖K v‖^2)/Real.sqrt (s^2+‖z‖^2+‖K z‖^2) ≤
      extDeriv (ExteriorForms.dc (fun _ => K) (hermitianSqrtPotential K s)) z ![v,K v] := by
  have hc := hermitianSqrtPotential_smooth K hs
  have hd : DifferentiableAt ℝ (fderiv ℝ (hermitianSqrtPotential K s)) z :=
    (hc.fderiv_right (m := ∞) (by simp)).differentiable (by simp) z
  rw [constant_ddc_trace K hK hd]
  change _ ≤ fderiv ℝ (fderiv ℝ (fun x => sqrtPotential s (hermitianGraph K x))) z v v +
    fderiv ℝ (fderiv ℝ (fun x => sqrtPotential s (hermitianGraph K x))) z (K v) (K v)
  rw [linear_pullback_hessian _ (sqrtPotential_smooth hs),
    linear_pullback_hessian _ (sqrtPotential_smooth hs)]
  obtain ⟨ho,hn⟩ := hermitianGraph_complex_pair K hK v
  have h := sqrtPotential_trace_lower hs (hermitianGraph K z)
    (hermitianGraph K v) (hermitianGraph K (K v)) ho hn
  simpa only [hermitianGraph_norm_sq,add_assoc] using h

end TamingCompatibility.RadialPotential

end

end OAI
