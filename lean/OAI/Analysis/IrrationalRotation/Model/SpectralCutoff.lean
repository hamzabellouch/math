import OAI.Analysis.IrrationalRotation.Model.FieldDiagonal
import OAI.Analysis.IrrationalRotation.Model.FieldUnboundedMultiplier
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Invariant233.WeightedShift.SpectralCutoff
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def boundedWeight (a : X → ℤ → ℂ) (C : ℝ)
    (ha : ∀ x k, ‖a x k‖ ≤ C) (x : X) : Weight :=
  ⟨a x, memℓp_infty ⟨C, by rintro r ⟨k, rfl⟩; exact ha x k⟩⟩

def boundedOperator (a : X → ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ x k, ‖a x k‖ ≤ C)
    (hm : ∀ k, AEStronglyMeasurable (fun x => a x k) μ) :
    FieldHilbert μ →L[ℂ] FieldHilbert μ :=
  fieldDiagonal (boundedWeight a C ha) C hC
    (fun x => lp.norm_le_of_forall_le hC (ha x)) hm

def window (n : ℕ) : Set ℝ := Set.Icc ((n + 1 : ℝ)⁻¹) (n + 1 : ℝ)

def symbol (n : ℕ) (r : ℝ) : ℂ := (window n).indicator (fun _ => 1) r

theorem norm_symbol_le (n : ℕ) (r : ℝ) : ‖symbol n r‖ ≤ 1 := by
  classical
  by_cases hr : r ∈ window n
  · simp [symbol, hr]
  · simp [symbol, hr]

def projection (h : X → ℤ → ℝ) (hm : ∀ k, Measurable (fun x => h x k))
    (n : ℕ) : FieldHilbert μ →L[ℂ] FieldHilbert μ :=
  boundedOperator (fun x k => symbol n (h x k)) 1 (by norm_num)
    (fun x k => norm_symbol_le n (h x k))
    (fun k => ((measurable_const.indicator measurableSet_Icc).comp (hm k)).aestronglyMeasurable)

def productSymbol (n : ℕ) (r : ℝ) : ℂ := (r : ℂ) * symbol n r

def inverseSymbol (n : ℕ) (r : ℝ) : ℂ := (r⁻¹ : ℝ) * symbol n r

theorem norm_productSymbol_le (n : ℕ) (r : ℝ) :
    ‖productSymbol n r‖ ≤ n + 1 := by
  classical
  by_cases hr : r ∈ window n
  · have hr0 : 0 ≤ r := le_trans (by positivity) hr.1
    simpa [productSymbol, symbol, hr, Complex.norm_real, abs_of_nonneg hr0] using hr.2
  · simp [productSymbol, symbol, hr]; positivity

theorem norm_inverseSymbol_le (n : ℕ) (r : ℝ) :
    ‖inverseSymbol n r‖ ≤ n + 1 := by
  classical
  by_cases hr : r ∈ window n
  · have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr.1
    have hbound : r⁻¹ ≤ n + 1 := (inv_le_comm₀ hr0 (by positivity)).mpr hr.1
    simpa [inverseSymbol, symbol, hr, Complex.norm_real, abs_of_pos hr0] using hbound
  · simp [inverseSymbol, symbol, hr]; positivity

def productOperator (h : X → ℤ → ℝ) (hm : ∀ k, Measurable (fun x => h x k))
    (n : ℕ) : FieldHilbert μ →L[ℂ] FieldHilbert μ :=
  boundedOperator (fun x k => productSymbol n (h x k)) (n + 1) (by positivity)
    (fun x k => norm_productSymbol_le n (h x k))
    (fun k => ((Complex.measurable_ofReal.comp (hm k)).mul
      ((measurable_const.indicator measurableSet_Icc).comp (hm k))).aestronglyMeasurable)

def inverseOperator (h : X → ℤ → ℝ) (hm : ∀ k, Measurable (fun x => h x k))
    (n : ℕ) : FieldHilbert μ →L[ℂ] FieldHilbert μ :=
  boundedOperator (fun x k => inverseSymbol n (h x k)) (n + 1) (by positivity)
    (fun x k => norm_inverseSymbol_le n (h x k))
    (fun k => ((Complex.measurable_ofReal.comp (hm k).inv).mul
      ((measurable_const.indicator measurableSet_Icc).comp (hm k))).aestronglyMeasurable)

def cutoffSpace (h : X → ℤ → ℝ) (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ) :
    Submodule ℂ (FieldHilbert μ) := (projection h hm n).range.topologicalClosure

instance cutoffSpace_hasOrthogonalProjection (h : X → ℤ → ℝ)
    (hm : ∀ k, Measurable (fun x => h x k)) (n : ℕ) :
    (cutoffSpace (μ := μ) h hm n).HasOrthogonalProjection := by
  let : IsClosed (cutoffSpace (μ := μ) h hm n : Set (FieldHilbert μ)) :=
    Submodule.isClosed_topologicalClosure _
  infer_instance

end Invariant233.WeightedShift.SpectralCutoff

end

end OAI
