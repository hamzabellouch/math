import Mathlib
import OAI.Analysis.Conductivity.Scalarization.SmoothScalarAlgebra

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity

theorem smoothDirection_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) (f g : SmoothScalar E) :
    smoothDirection v (f * g) = f * smoothDirection v g + g * smoothDirection v f := by
  apply Subtype.ext
  funext x
  change fderiv ℝ (f.val * g.val) x v =
    f.val x * fderiv ℝ g.val x v + g.val x * fderiv ℝ f.val x v
  rw [fderiv_mul ((smoothScalar_contDiff f).differentiable (by simp) x)
    ((smoothScalar_contDiff g).differentiable (by simp) x)]
  rfl

def smoothPhase {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) : SmoothScalar ℝ →ₐ[ℝ] SmoothScalar E where
  toFun H := ⟨H.val ∘ L, by
    change ContDiff ℝ (↑(⊤ : ℕ∞)) _
    exact (smoothScalar_contDiff H).comp L.contDiff⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp] theorem smoothPhase_apply {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (L : E →L[ℝ] ℝ) (H : SmoothScalar ℝ) (x : E) :
    (smoothPhase L H).val x = H.val (L x) := rfl

theorem smoothDirection_phase {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) (L : E →L[ℝ] ℝ) (H : SmoothScalar ℝ) :
    smoothDirection v (smoothPhase L H) = L v • smoothPhase L (smoothDirection 1 H) := by
  apply Subtype.ext
  funext x
  change fderiv ℝ (H.val ∘ L) x v = L v * fderiv ℝ H.val (L x) 1
  rw [fderiv_comp x ((smoothScalar_contDiff H).differentiable (by simp) (L x))
    L.differentiableAt, L.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  simpa only [smul_eq_mul, mul_one] using (fderiv ℝ H.val (L x)).map_smul (L v) 1

end ScalarConductivity

end

end OAI
