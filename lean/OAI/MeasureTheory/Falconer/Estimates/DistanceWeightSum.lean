import OAI.MeasureTheory.Falconer.Angular.GraphRotatedWeights

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem graphDistanceWeight_norm_total {m : ℕ} (hm : 0 < m)
    (axis : ℝ) (p : UnitCircle × UnitCircle) :
    (∑ j ∈ Finset.range m, ∑ k ∈ Finset.range m, ‖graphDistanceWeight axis m j k p‖) =
      ‖sourceConeCircle axis p.1‖ * ‖sourceConeCircle axis p.2‖ := by
  simp only [graphDistanceWeight,norm_mul,Complex.norm_conj,Complex.norm_real,
    Real.norm_eq_abs,
    graphBinWeight,abs_of_nonneg (circleAngularBin_bounds _ _ _).1,← Finset.sum_mul,← Finset.mul_sum,circleAngularBin_partition hm,one_mul,mul_one]

theorem graphRotatedDistanceWeight_norm_total_le {m : ℕ} (hm : 0 < m)
    (axis : ℝ) (p : UnitCircle × UnitCircle) :
    (∑ j ∈ Finset.range m, ∑ k ∈ Finset.range m, ‖graphRotatedDistanceWeight axis m j k p‖) ≤ 1 := by
  rw [show (∑ j ∈ Finset.range m, ∑ k ∈ Finset.range m, ‖graphRotatedDistanceWeight axis m j k p‖) =
      ‖sourceConeCircle 0 (sourceCircleRotate (-axis) p.1)‖ *
      ‖sourceConeCircle 0 (sourceCircleRotate (-axis) p.2)‖ from graphDistanceWeight_norm_total hm 0 _]
  exact (mul_le_mul (sourceConeCircle_norm_le _ _) (sourceConeCircle_norm_le _ _)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

end PlanarFalconer

end OAI
