import OAI.MeasureTheory.Falconer.Slicing.GaussianBox

namespace OAI

/-! # A uniform positive incidence threshold on the bounded parameter box -/

namespace Falconer
open MeasureTheory
open scoped ENNReal

noncomputable def gaussianSelectionThreshold (h : ℕ) (K Z : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1/(4*K*(2*Z)^h))

theorem gaussianSelectionThreshold_pos (h : ℕ) {K Z : ℝ} (hK : 0 < K) (hZ : 0 < Z) :
    0 < gaussianSelectionThreshold h K Z := by
  apply ENNReal.ofReal_pos.mpr
  positivity

theorem gaussianSelectionThreshold_budget (h : ℕ) {K Z : ℝ} (hK : 0 < K) (hZ : 0 < Z) :
    gaussianSelectionThreshold h K Z * volume (coordinateBox h Z) =
      ENNReal.ofReal (1/(4*K)) := by
  rw [gaussianSelectionThreshold,coordinateBox_volume hZ.le,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

theorem gaussianSelectionThreshold_uniform (h : ℕ) {K Z Z₀ : ℝ}
    (hK : 0 < K) (hZ₀ : 0 < Z₀) (hZZ : Z ≤ Z₀) :
    gaussianSelectionThreshold h K Z₀ * volume (coordinateBox h Z) ≤
      ENNReal.ofReal (1/(4*K)) := by
  have hsub : coordinateBox h Z ⊆ coordinateBox h Z₀ := fun x hx i => (hx i).trans hZZ
  exact (mul_le_mul' le_rfl (measure_mono hsub)).trans_eq (gaussianSelectionThreshold_budget h hK hZ₀)

end Falconer

end OAI
