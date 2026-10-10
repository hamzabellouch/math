import OAI.Geometry.RCD.Harmonic.PointedRadialDistance

namespace OAI

/-! # The prescribed squared-radius values belong to the actual local L2 space -/

open Set Metric Filter MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem measured_radial_memLp (μ : Measure X) {n : ℕ} {p : X} {r S ε : ℝ}
    (hr : 0<r) (hS : 0≤S) (V : X → Euclidean n)
    [IsFiniteMeasure (μ.restrict (ball p (S*r)))]
    (hV : IsMeasuredEuclideanApproximation μ n p r S ε V) :
    MemLp (fun x => ‖V x‖^2/2) 2 (μ.restrict (ball p (S*r))) := by
  have hε : 0≤ε := dist_nonneg.trans hV.metric.1
  apply MemLp.of_bound (((continuous_norm.pow 2).div_const 2).measurable.comp hV.measurable).aestronglyMeasurable
    ((S+2*ε)^2/2)
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  have hd := (abs_le.mp (pointed_radial_distance hr hS hV.metric hx.le)).2
  have hdr : dist x p/r≤S := (div_le_iff₀ hr).mpr hx.le
  have hnx : ‖V x‖≤S+2*ε := by linarith
  rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (sq_nonneg _) (by norm_num))]
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hnx 2) (by norm_num)

end RegularPointCoordinates

end

end OAI
