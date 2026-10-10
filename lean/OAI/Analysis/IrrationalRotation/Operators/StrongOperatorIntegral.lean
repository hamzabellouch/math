import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.Basic

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.StrongOperatorIntegral

variable {X E F : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {μ : Measure X} [IsProbabilityMeasure μ]

def linearMap (A : X → E →L[ℂ] F)
    (hint : ∀ v, Integrable (fun x => A x v) μ) : E →ₗ[ℂ] F where
  toFun v := ∫ x, A x v ∂μ
  map_add' v w := by
    simp only [map_add]
    exact integral_add (hint v) (hint w)
  map_smul' c v := by
    simp only [map_smul]
    exact integral_smul c (fun x => A x v)

omit [CompleteSpace F] in

theorem norm_linearMap_le (A : X → E →L[ℂ] F)
    (hint : ∀ v, Integrable (fun x => A x v) μ)
    {C : ℝ} (hbound : ∀ᵐ x ∂μ, ‖A x‖ ≤ C) (v : E) :
    ‖linearMap A hint v‖ ≤ C * ‖v‖ := by
  change ‖∫ x, A x v ∂μ‖ ≤ C * ‖v‖
  have h := norm_integral_le_of_norm_le_const (μ := μ)
    (C := C * ‖v‖) (f := fun x => A x v) (by
      filter_upwards [hbound] with x hx
      exact ((A x).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right hx (norm_nonneg v)))
  simpa using h

def operator (A : X → E →L[ℂ] F)
    (hint : ∀ v, Integrable (fun x => A x v) μ)
    (C : ℝ) (hbound : ∀ᵐ x ∂μ, ‖A x‖ ≤ C) : E →L[ℂ] F :=
  (linearMap A hint).mkContinuous C (norm_linearMap_le A hint hbound)

omit [CompleteSpace F] in
@[simp] theorem operator_apply (A : X → E →L[ℂ] F)
    (hint : ∀ v, Integrable (fun x => A x v) μ)
    (C : ℝ) (hbound : ∀ᵐ x ∂μ, ‖A x‖ ≤ C) (v : E) :
    operator A hint C hbound v = ∫ x, A x v ∂μ := rfl

omit [CompleteSpace F] in
theorem norm_operator_le (A : X → E →L[ℂ] F)
    (hint : ∀ v, Integrable (fun x => A x v) μ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ᵐ x ∂μ, ‖A x‖ ≤ C) :
    ‖operator A hint C hbound‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

theorem test_operator (L : F →L[ℂ] G) (A : X → E →L[ℂ] F)
    (hint : ∀ v, Integrable (fun x => A x v) μ)
    (C : ℝ) (hbound : ∀ᵐ x ∂μ, ‖A x‖ ≤ C) (v : E) :
    L (operator A hint C hbound v) = ∫ x, L (A x v) ∂μ :=
  (L.integral_comp_comm (hint v)).symm

end Invariant233.StrongOperatorIntegral

end

end OAI
