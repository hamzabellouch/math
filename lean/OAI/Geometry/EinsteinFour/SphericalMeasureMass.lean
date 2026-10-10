import OAI.Geometry.EinsteinFour.SphericalMeasureCharts

namespace OAI

/-! Finite positive mass of the actual Hausdorff measure on the unit
three-sphere, and hence the probability normalization used by the moments. -/

namespace PositiveEinsteinFour.Angular

open EinsteinFour MeasureTheory
open scoped BigOperators

noncomputable section

private theorem threeSpace_hausdorff_haar :
    Measure.IsAddHaarMeasure (Measure.hausdorffMeasure 3 : Measure ThreeSpace) := by
  simpa [ThreeSpace] using
    (inferInstance : Measure.IsAddHaarMeasure
      (Measure.hausdorffMeasure (Module.finrank ℝ ThreeSpace) : Measure ThreeSpace))

/-- Compact smooth face images have finite three-dimensional measure. -/
theorem faceChart_measure_lt_top (i : Fin 4) (t : Bool) :
    (Measure.hausdorffMeasure 3 : Measure FourSpace)
      (faceChart i t '' Metric.closedBall (0 : ThreeSpace) 2) < ⊤ := by
  let _ := threeSpace_hausdorff_haar
  obtain ⟨K, hK⟩ := faceChart_lipschitz i t
  have hB : (Measure.hausdorffMeasure 3 : Measure ThreeSpace)
      (Metric.closedBall 0 2) < ⊤ := (isCompact_closedBall _ _).measure_lt_top
  refine lt_of_le_of_lt (hK.hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 3)) ?_
  rw [show (3 : ℝ) = (3 : ℕ) by norm_num, ENNReal.rpow_natCast]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hB

theorem sphere_hausdorff_measure_lt_top :
    (Measure.hausdorffMeasure 3 : Measure FourSpace) {v | ‖v‖ = 1} < ⊤ := by
  have hc : {v : FourSpace | ‖v‖ = 1} ⊆
      ⋃ a : Fin 4 × Bool, faceChart a.1 a.2 '' Metric.closedBall (0 : ThreeSpace) 2 := by
    intro v hv
    obtain ⟨i, t, u, hu, he⟩ := exists_faceChart ⟨v, hv⟩
    exact Set.mem_iUnion.mpr ⟨(i,t), u, hu, he⟩
  apply lt_of_le_of_lt (measure_mono hc)
  simpa only [Set.biUnion_univ] using
    (measure_biUnion_lt_top (μ := (Measure.hausdorffMeasure 3 : Measure FourSpace))
      (s := (Set.univ : Set (Fin 4 × Bool))) Set.finite_univ
      (fun a _ => faceChart_measure_lt_top a.1 a.2))

theorem sphere_hausdorff_measure_pos :
    0 < (Measure.hausdorffMeasure 3 : Measure FourSpace) {v | ‖v‖ = 1} := by
  let _ := threeSpace_hausdorff_haar
  have hb : 0 < (Measure.hausdorffMeasure 3 : Measure ThreeSpace)
      (Metric.ball (0 : ThreeSpace) 1) :=
    Metric.isOpen_ball.measure_pos _ (Metric.nonempty_ball.mpr (by norm_num))
  have hp := tailProjection_lipschitz.hausdorffMeasure_image_le
    (by norm_num : (0 : ℝ) ≤ 3) {v : FourSpace | ‖v‖ = 1}
  simp only [ENNReal.coe_one, ENNReal.one_rpow, one_mul] at hp
  exact lt_of_lt_of_le (lt_of_lt_of_le hb (measure_mono ball_subset_tailProjection_sphere)) hp

/-- Hausdorff measure on the subtype agrees with the ambient measure. -/
theorem direction_hausdorff_mass_eq :
    (Measure.hausdorffMeasure 3 : Measure Directions) Set.univ =
      (Measure.hausdorffMeasure 3 : Measure FourSpace) {v | ‖v‖ = 1} := by
  have hr : (Subtype.val : Directions → FourSpace) '' Set.univ = {v | ‖v‖ = 1} := by
    ext v
    simp
  rw [← hr]
  exact (Isometry.hausdorffMeasure_image
    (show Isometry (Subtype.val : Directions → FourSpace) from isometry_subtype_coe)
    (Or.inl (by norm_num : (0 : ℝ) ≤ 3)) Set.univ).symm

theorem direction_hausdorff_mass_pos :
    0 < (Measure.hausdorffMeasure 3 : Measure Directions) Set.univ := by
  rw [direction_hausdorff_mass_eq]
  exact sphere_hausdorff_measure_pos

theorem direction_hausdorff_mass_lt_top :
    (Measure.hausdorffMeasure 3 : Measure Directions) Set.univ < ⊤ := by
  rw [direction_hausdorff_mass_eq]
  exact sphere_hausdorff_measure_lt_top

/-- The concrete normalization is a genuine probability measure. -/
theorem actual_sphereMeasure_probability : IsProbabilityMeasure sphereMeasure := by
  constructor
  unfold sphereMeasure
  rw [Measure.smul_apply, smul_eq_mul,
    ENNReal.inv_mul_cancel direction_hausdorff_mass_pos.ne'
      direction_hausdorff_mass_lt_top.ne]

end
end PositiveEinsteinFour.Angular

end OAI
