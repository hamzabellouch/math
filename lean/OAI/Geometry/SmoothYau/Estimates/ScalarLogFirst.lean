import Mathlib

namespace OAI

noncomputable section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma scalarLog_first {q : E → ℝ} {x : E} (hq : DifferentiableAt ℝ q x) (hx : q x ≠ 0) (v : E) :
    fderiv ℝ (fun y => Real.log (q y)) x v = (q x)⁻¹*fderiv ℝ q x v := by
  rw [(hq.hasFDerivAt.log hx).fderiv]
  rfl
lemma scalarLog_second {q : E → ℝ} (hq : ContDiff ℝ ∞ q) {x : E} (hx : q x ≠ 0) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => Real.log (q y))) x v w =
      (q x)⁻¹*fderiv ℝ (fderiv ℝ q) x v w - (q x)⁻¹^2*fderiv ℝ q x v*fderiv ℝ q x w := by
  have he : (fun y => fderiv ℝ (fun z => Real.log (q z)) y) =ᶠ[𝓝 x]
      (fun y => (q y)⁻¹ • fderiv ℝ q y) := by
    filter_upwards [hq.continuous.continuousAt.eventually_ne hx] with y hy
    exact ((hq.differentiable (by simp) y).hasFDerivAt.log hy).fderiv
  rw [he.fderiv_eq]
  have hi := (hasFDerivAt_inv hx).comp x (hq.differentiable (by simp) x).hasFDerivAt
  have hD := ((hq.fderiv_right (m:=∞) (by simp)).differentiable (by simp) x).hasFDerivAt
  change fderiv ℝ ((((fun t : ℝ => t⁻¹) ∘ q) • fderiv ℝ q)) x v w = _
  rw [(hi.smul hD).fderiv]
  simp only [add_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply,Function.comp_apply,inv_pow,smul_eq_mul]
  ring
lemma directional_clm_comp_general {F V : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (L : E →L[ℝ] F) {f : F → V}
    (hf : Differentiable ℝ f) (x v : E) :
    fderiv ℝ (f ∘ L) x v = fderiv ℝ f (L x) (L v) := by
  rw [fderiv_comp x (hf _) L.differentiableAt,L.fderiv]
  rfl
lemma second_clm_comp_general {F V : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (L : E →L[ℝ] F) {f : F → V}
    (hf : ContDiff ℝ ∞ f) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ (f ∘ L) y w) x v =
      fderiv ℝ (fun y => fderiv ℝ f y (L w)) (L x) (L v) := by
  simp_rw [directional_clm_comp_general L (hf.differentiable (by simp))]
  exact directional_clm_comp_general L
    (((hf.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const).differentiable (by simp)) x v
end YauCounterexamples
end

end OAI
