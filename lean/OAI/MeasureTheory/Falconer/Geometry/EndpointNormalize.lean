import OAI.MeasureTheory.Falconer.Slicing.SliceNormalization
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

/-! # Normalization costs for the endpoint direction law -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem normalizedSliceLaw_power_bound (ν : Measure Y) [IsFiniteMeasure ν]
    (hν : ν univ ≠ 0) {δ σ ε q r : ℝ} (hδ : 0 < δ) (_hr : 0 ≤ r)
    (hmass : ENNReal.ofReal (δ^σ) ≤ ν univ) (S : Set Y)
    (hS : ν S ≤ ENNReal.ofReal (δ^(-ε)*r^q)) :
    (normalizedSliceLaw ν hν : Measure Y) S ≤ ENNReal.ofReal (δ^(-ε-σ)*r^q) := by
  apply (normalizedSliceLaw_bound ν hν S hmass hS).trans_eq
  rw [← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hδ σ),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [← Real.rpow_neg hδ.le]
  calc
    _ = (δ^(-ε)*δ^(-σ))*r^q := by ring
    _ = _ := by rw [← Real.rpow_add hδ]; congr 2

theorem incidence_le_normalized_direction (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [IsFiniteMeasure ν] (hν : ν univ ≠ 0) (hmass : ν univ ≤ 1)
    (E : Set (X × Y)) :
    (μ.prod ν) E ≤ (μ.prod (normalizedSliceLaw ν hν : Measure Y)) E := by
  change (μ.prod ν) E ≤ (μ.prod ((ν univ)⁻¹ • ν)) E
  rw [Measure.prod_smul_right,Measure.smul_apply,smul_eq_mul]
  have hi : 1 ≤ (ν univ)⁻¹ := by
    simpa only [inv_one] using ENNReal.inv_le_inv.mpr hmass
  simpa only [one_mul,mul_one,mul_comm] using mul_le_mul_right hi ((μ.prod ν) E)

end Falconer

end OAI
