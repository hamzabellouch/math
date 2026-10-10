import OAI.Geometry.RCD.Metric.HausdorffOpenUpper

namespace OAI

/-! # The normalized Euclidean Hausdorff measure is bounded by volume -/

open Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates

theorem normalized_hausdorff_le_volume {n : ℕ} (hn : 0 < n) :
    hausdorff n (Euclidean n) ≤ volume := by
  have hω0 : volume (ball (0 : Euclidean n) 1) ≠ 0 :=
    (measure_ball_pos volume 0 zero_lt_one).ne'
  have hωtop : volume (ball (0 : Euclidean n) 1) ≠ ⊤ := measure_ball_ne_top
  have htwo0 : (2:ℝ≥0∞)^n ≠ 0 := by positivity
  have htwotop : (2:ℝ≥0∞)^n ≠ ⊤ := by finiteness
  have hopen (U : Set (Euclidean n)) (hU : IsOpen U) :
      hausdorff n (Euclidean n) U ≤ volume U := by
    have hh := raw_hausdorff_open_upper hn hU
    change (volume (ball (0 : Euclidean n) 1)/(2:ℝ≥0∞)^n)*
      Measure.hausdorffMeasure (n:ℝ) U ≤ volume U
    calc
      _ ≤ (volume (ball (0 : Euclidean n) 1)/(2:ℝ≥0∞)^n)*
          (((2:ℝ≥0∞)^n/volume (ball (0 : Euclidean n) 1))*volume U) := by gcongr
      _ = volume U := by
        rw [div_eq_mul_inv,div_eq_mul_inv]
        calc
          _ = ((volume (ball (0 : Euclidean n) 1)*
              (volume (ball (0 : Euclidean n) 1))⁻¹)*
              (((2:ℝ≥0∞)^n)⁻¹*(2:ℝ≥0∞)^n))*volume U := by ac_rfl
          _ = _ := by rw [ENNReal.mul_inv_cancel hω0 hωtop,
            ENNReal.inv_mul_cancel htwo0 htwotop,one_mul,one_mul]
  intro A
  rw [A.measure_eq_iInf_isOpen volume]
  apply le_iInf
  intro U
  apply le_iInf
  intro hAU
  apply le_iInf
  intro hU
  exact (measure_mono hAU).trans (hopen U hU)

end RegularPointCoordinates

end

end OAI
