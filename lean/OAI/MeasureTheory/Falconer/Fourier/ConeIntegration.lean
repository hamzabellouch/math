import OAI.MeasureTheory.Falconer.Angular.GnomonicInverse
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! # Coordinate and dilation integration for the gnomonic cone formula -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

noncomputable def euclideanTail {n : ℕ} (z : Space (n+1)) : Space n :=
  WithLp.toLp 2 (fun i => z i.succ)

theorem euclidean_coordinate_split_preserving (n : ℕ) :
    MeasurePreserving (fun z : Space (n+1) => (z 0,euclideanTail z))
      volume ((volume : Measure ℝ).prod (volume : Measure (Space n))) := by
  have h₁ := PiLp.volume_preserving_ofLp (Fin (n+1))
  have h₂ := volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
  have h₃ := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (PiLp.volume_preserving_toLp (Fin n))
  exact h₃.comp (h₂.comp h₁)

theorem lintegral_euclidean_coordinate_split {n : ℕ}
    (f : ℝ × Space n → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z : Space (n+1), f (z 0,euclideanTail z)) = ∫⁻ r : ℝ, ∫⁻ x : Space n, f (r,x) := by
  rw [(euclidean_coordinate_split_preserving n).lintegral_comp hf]
  exact lintegral_prod _ hf.aemeasurable

theorem lintegral_inverse_dilation {n : ℕ} (r : ℝ) (hr : 0 < r)
    (f : Space n → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ y : Space n, f (r⁻¹ • y)) = ENNReal.ofReal (r^n)*(∫⁻ x : Space n, f x) := by
  rw [← lintegral_map hf (measurable_const_smul r⁻¹),
    Measure.map_addHaar_smul volume (inv_ne_zero hr.ne'),lintegral_smul_measure]
  congr 1
  simp only [inv_pow,inv_inv]
  rw [abs_of_nonneg (pow_nonneg hr.le _)]
  simp [Space]

end Falconer

end OAI
