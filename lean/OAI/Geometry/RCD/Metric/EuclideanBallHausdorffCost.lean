import OAI.Geometry.RCD.Sobolev.EuclideanEnergyRatios
import Mathlib.MeasureTheory.Measure.Hausdorff

namespace OAI

/-! # The diameter cost of a Euclidean ball and absolute continuity -/

open Set Metric MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates

theorem closedBall_ediam_le_twice {E : Type*} [MetricSpace E]
    (x : E) (r : ℝ) : ediam (closedBall x r) ≤ ENNReal.ofReal (2*r) := by
  apply ediam_le
  intro y hy z hz
  rw [edist_dist]
  apply ENNReal.ofReal_le_ofReal
  have ht := dist_triangle y x z
  have hyx := mem_closedBall.mp hy
  have hzx := mem_closedBall.mp hz
  rw [dist_comm x z] at ht
  linarith only [ht,hyx,hzx]

theorem raw_hausdorff_absolutelyContinuous {n : ℕ} :
    (Measure.hausdorffMeasure (n:ℝ) : Measure (Euclidean n)) ≪ volume := by
  have hi : Measure.IsAddHaarMeasure (Measure.hausdorffMeasure (n:ℝ) : Measure (Euclidean n)) := by
    simpa only [finrank_euclideanSpace_fin] using
      (inferInstance : Measure.IsAddHaarMeasure
        (Measure.hausdorffMeasure (Module.finrank ℝ (Euclidean n)) : Measure (Euclidean n)))
  let : Measure.IsAddHaarMeasure (Measure.hausdorffMeasure (n:ℝ) : Measure (Euclidean n)) := hi
  exact Measure.absolutelyContinuous_isAddHaarMeasure _ _

theorem euclidean_ball_diameter_cost {n : ℕ} (hn : 0 < n)
    (x : Euclidean n) {r : ℝ} (hr : 0 < r) :
    ediam (closedBall x r)^(n:ℝ) ≤
      ((2:ℝ≥0∞)^n/volume (ball (0 : Euclidean n) 1))*volume (closedBall x r) := by
  let : NeZero n := ⟨hn.ne'⟩
  have hω0 : volume (ball (0 : Euclidean n) 1) ≠ 0 :=
    (measure_ball_pos volume 0 zero_lt_one).ne'
  have hωtop : volume (ball (0 : Euclidean n) 1) ≠ ⊤ := measure_ball_ne_top
  have hv : volume (closedBall x r) =
      (ENNReal.ofReal r)^n*volume (ball (0 : Euclidean n) 1) := by
    rw [Measure.addHaar_closedBall_eq_addHaar_ball,
      Measure.addHaar_ball volume x hr.le,finrank_euclideanSpace_fin,ENNReal.ofReal_pow hr.le]
  rw [ENNReal.rpow_natCast]
  calc
    ediam (closedBall x r)^n ≤ (ENNReal.ofReal (2*r))^n :=
      pow_le_pow_left' (closedBall_ediam_le_twice x r) n
    _ = (2:ℝ≥0∞)^n*(ENNReal.ofReal r)^n := by
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),ENNReal.ofReal_ofNat,mul_pow]
    _ = _ := by
      rw [hv,div_eq_mul_inv]
      calc
        _ = (2:ℝ≥0∞)^n*(ENNReal.ofReal r)^n*
            ((volume (ball (0 : Euclidean n) 1))⁻¹*volume (ball (0 : Euclidean n) 1)) := by
              rw [ENNReal.inv_mul_cancel hω0 hωtop,mul_one]
        _ = _ := by ac_rfl

end RegularPointCoordinates

end

end OAI
