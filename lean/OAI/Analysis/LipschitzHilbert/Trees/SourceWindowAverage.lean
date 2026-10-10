import OAI.Analysis.LipschitzHilbert.Trees.SourceLineWindow
import OAI.Analysis.LipschitzHilbert.Phase.SourceGridPrediction

namespace OAI

/-! Convert the constructed probability-normalized source factors to
Lebesgue cell averages on the exact local line windows. -/

noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.FiniteLineGrid

private theorem window_probability (g : FiniteLineGrid) :
    intervalProbability g.origin (g.origin+g.width) =
      (ENNReal.ofReal g.width)⁻¹ • volume.restrict g.root := by
  unfold intervalProbability root
  rw [show g.origin+g.width-g.origin = g.width by ring,
    restrict_Ico_eq_restrict_Icc]

theorem window_integrable_iff (g : FiniteLineGrid) (F : ℝ → ℝ) :
    Integrable F (intervalProbability g.origin (g.origin+g.width)) ↔
      IntegrableOn F g.root volume := by
  rw [window_probability]
  exact integrable_smul_measure (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
    (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr g.width_pos))

theorem window_probability_integral (g : FiniteLineGrid) (F : ℝ → ℝ) :
    (∫ x, F x ∂intervalProbability g.origin (g.origin+g.width)) =
      (g.width)⁻¹*(∫ x in g.root, F x) := by
  rw [window_probability,integral_smul_measure,ENNReal.toReal_inv,
    ENNReal.toReal_ofReal g.width_pos.le,smul_eq_mul]

/-- The constructed normalized factor has the required ordinary cell
average, with the half-open source window retained exactly. -/
theorem window_average_le (g : FiniteLineGrid) (F : ℝ → ℝ)
    (hint : Integrable F (intervalProbability g.origin (g.origin+g.width)))
    (havg : (∫ x, F x ∂intervalProbability g.origin (g.origin+g.width)) ≤ 1) :
    IntegrableOn F g.root volume ∧
      (∫ x in g.root, F x) ≤ volume.real g.root := by
  refine ⟨(g.window_integrable_iff F).mp hint,?_⟩
  have hwidth : volume.real g.root = g.width := by
    rw [measureReal_def,root,Real.volume_Ico]
    rw [show g.origin+g.width-g.origin = g.width by ring,
      ENNReal.toReal_ofReal g.width_pos.le]
  rw [hwidth]
  calc
    _ = g.width*(∫ x, F x ∂intervalProbability g.origin (g.origin+g.width)) := by
      rw [g.window_probability_integral]
      field_simp [ne_of_gt g.width_pos]
    _ ≤ g.width*1 := mul_le_mul_of_nonneg_left havg g.width_pos.le
    _ = _ := mul_one _

end LipschitzHilbert.FiniteLineGrid

end

end OAI
