import Mathlib
import OAI.Analysis.RieszRectifiability.Rigidity.PlaneHeightDistribution

namespace OAI

/-!
# Ambient extensions of affine plane heights

The adjoint of a linear isometric embedding extends an affine height from plane
coordinates to the ambient space. Its operator norms give a Lipschitz bound,
and the pullback identity transfers almost-everywhere affine agreement to the
coordinate plane measure.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory
open scoped NNReal

def ambientAffineHeight {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (c : ℝ) (M : Ambient n →L[ℝ] ℝ)
    (x : Ambient d) : ℝ := c + M (L.toContinuousLinearMap.adjoint (x - a))

theorem ambientAffineHeight_lipschitz {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (c : ℝ) (M : Ambient n →L[ℝ] ℝ) :
    LipschitzWith (‖M‖₊ * ‖L.toContinuousLinearMap.adjoint‖₊) (ambientAffineHeight a L c M) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [ambientAffineHeight, dist_add_left, NNReal.coe_mul, coe_nnnorm]
  calc
    _ ≤ ‖M‖ * dist (L.toContinuousLinearMap.adjoint (x - a))
        (L.toContinuousLinearMap.adjoint (y - a)) := M.lipschitzWith.dist_le_mul _ _
    _ ≤ ‖M‖ * (‖L.toContinuousLinearMap.adjoint‖ * dist (x - a) (y - a)) :=
      mul_le_mul_of_nonneg_left (L.toContinuousLinearMap.adjoint.lipschitzWith.dist_le_mul _ _)
        (norm_nonneg _)
    _ = _ := by rw [dist_sub_right]; ring

theorem ambientAffineHeight_pullback {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (c : ℝ) (M : Ambient n →L[ℝ] ℝ) (x : Ambient n) :
    ambientAffineHeight a L c M (a + L x) = c + M x := by
  have h : L.toContinuousLinearMap.adjoint (L x) = x :=
    DFunLike.congr_fun L.adjoint_comp_self x
  simp only [ambientAffineHeight, add_sub_cancel_left, h]

theorem height_ae_eq_ambient_affine {n d : ℕ} (a : Ambient d)
    (L : Ambient n →ₗᵢ[ℝ] Ambient d) (f : Ambient d → ℝ) (hfm : Measurable f)
    (c : ℝ) (M : Ambient n →L[ℝ] ℝ)
    (hf : ∀ᵐ x, f (a + L x) = c + M x) :
    f =ᵐ[coordinatePlaneMeasure (affinePlaneSection a L)] ambientAffineHeight a L c M := by
  rw [coordinatePlaneMeasure_affine_eq_map]
  have he : Measurable (fun x : Ambient n => a + L x) := by fun_prop
  have hm : MeasurableSet {x | f x = ambientAffineHeight a L c M x} :=
    measurableSet_eq_fun hfm (ambientAffineHeight_lipschitz a L c M).continuous.measurable
  apply (ae_map_iff he.aemeasurable hm).mpr
  filter_upwards [hf] with x hx
  simpa only [ambientAffineHeight_pullback] using! hx

end

end RieszRectifiability

end OAI
