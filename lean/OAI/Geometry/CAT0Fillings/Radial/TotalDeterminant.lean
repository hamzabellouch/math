import Mathlib
import OAI.Geometry.CAT0Fillings.Model
import OAI.Geometry.CAT0Fillings.Radial.TotalForm

namespace OAI

section
section
namespace CAT0Fillings
open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def metricTotalRadialForm (G : Matrix ι ι ℝ) (g r t : ℝ) (α γ : ι → ℝ) :
    Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℝ :=
  totalRankOneForm ((1-t*g)^2 • (G-vecMulVec α α)) (-r*g)
    ((1-t*g) • α-(t*r) • γ)

lemma metricTotalRadialForm_det (G : Matrix ι ι ℝ) (g r t : ℝ) (α γ : ι → ℝ)
    (hG : G.det ≠ 0) :
    (metricTotalRadialForm G g r t α γ).det =
      (r*g)^2*(1-t*g)^(2*Fintype.card ι)*G.det*(1-α ⬝ᵥ G⁻¹.mulVec α) := by
  rw [metricTotalRadialForm,totalRankOneForm_det,Matrix.det_smul,det_sub_vecMulVec G α hG]
  simp only [neg_mul,neg_sq,←pow_mul]
  ring

lemma metricTotalRadialForm_normalized_sqrt_det
    (G : Matrix ι ι ℝ) (g r t : ℝ) (α γ : ι → ℝ)
    (hG : G.PosDef) (hr : 0 ≤ r) (hg : 0 ≤ g) (hscale : 0 ≤ 1-t*g) :
    Real.sqrt (metricTotalRadialForm G g r t α γ).det / Real.sqrt G.det =
      r*g*(1-t*g)^Fintype.card ι * Real.sqrt (1-α ⬝ᵥ G⁻¹.mulVec α) := by
  have he : (metricTotalRadialForm G g r t α γ).det =
      (r*g*(1-t*g)^Fintype.card ι)^2 * G.det *(1-α ⬝ᵥ G⁻¹.mulVec α) := by
    rw [metricTotalRadialForm_det G g r t α γ hG.det_pos.ne']
    simp only [mul_pow,←pow_mul]
    ring
  rw [he,Real.sqrt_mul (mul_nonneg (sq_nonneg _) hG.det_pos.le),
    Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (mul_nonneg (mul_nonneg hr hg) (pow_nonneg hscale _))]
  have hJ : Real.sqrt G.det ≠ 0 := (Real.sqrt_pos.2 hG.det_pos).ne'
  field_simp

end CAT0Fillings

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings

attribute [local instance] Classical.propDecidable

universe u

end CAT0Fillings

open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

end
end

end OAI
