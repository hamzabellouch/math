import OAI.MeasureTheory.Falconer.Graphs.GraphActualTransport

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

noncomputable def graphRotatedDistanceWeight (axis : ℝ) (n j k : ℕ)
    (p : UnitCircle × UnitCircle) : ℂ :=
  graphDistanceWeight 0 n j k (sourceCircleRotate (-axis) p.1, sourceCircleRotate (-axis) p.2)

theorem graphRotatedDistanceWeight_eq (axis : ℝ) (n j k : ℕ) (u v : UnitCircle) :
    graphRotatedDistanceWeight axis n j k (u,v) =
      (sourceConeCircle axis u * rotatedBinSelection n {j} axis u) *
        conj (sourceConeCircle axis v * rotatedBinSelection n {k} axis v) := by
  simp only [graphRotatedDistanceWeight, graphDistanceWeight, graphBinWeight,
    rotatedBinSelection, Finset.sum_singleton, sourceConeCircle,
    neg_zero, sourceCircleRotate_zero, map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
  ring

theorem graphRotatedDistanceWeight_continuous (axis : ℝ) (n j k : ℕ) :
    Continuous (graphRotatedDistanceWeight axis n j k) :=
  (graphDistanceWeight_continuous 0 n j k).comp
    (((sourceCircleRotate_isometry (-axis)).continuous.comp continuous_fst).prodMk
      ((sourceCircleRotate_isometry (-axis)).continuous.comp continuous_snd))

theorem graphRotatedDistanceWeight_norm_le (axis : ℝ) (n j k : ℕ) (p : UnitCircle × UnitCircle) :
    ‖graphRotatedDistanceWeight axis n j k p‖ ≤ 1 := graphDistanceWeight_norm_le 0 n j k _

theorem graphRotatedDistanceWeight_parameter (axis : ℝ) (n j k : ℕ) (φ z : ℝ)
    (h : graphRotatedDistanceWeight axis n j k
      (sourceUnitDirection (φ+Real.arctan z), sourceUnitDirection (φ-Real.arctan z)) ≠ 0) :
    |z| ≤ 4 := by
  rw [graphRotatedDistanceWeight_eq] at h
  have hu : sourceConeCircle axis (sourceUnitDirection (φ+Real.arctan z)) ≠ 0 := by
    intro hz; exact h (by simp [hz])
  have hv : sourceConeCircle axis (sourceUnitDirection (φ-Real.arctan z)) ≠ 0 := by
    intro hz; exact h (by simp [hz])
  have hb := sourceConeCircle_plus_nondegenerate axis _ _ (subset_closure hu) (subset_closure hv)
  exact (graph_parameter_bound φ z ((by norm_num : (1/2:ℝ) ≤ 6/5).trans hb)).2

noncomputable def graphSourceWeight (distance plus : Bool) (axis : ℝ) (n j k : ℕ) :
    UnitCircle × UnitCircle → ℂ :=
  if distance then graphRotatedDistanceWeight axis n j k else graphProductWeight plus n j k

noncomputable def graphSourceChartAxis (distance plus : Bool) : ℝ :=
  if distance then 0 else if plus then 0 else Real.pi

theorem graphSourceWeight_continuous (distance plus : Bool) (axis : ℝ) (n j k : ℕ) :
    Continuous (graphSourceWeight distance plus axis n j k) := by
  cases distance
  · exact graphProductWeight_continuous plus n j k
  · exact graphRotatedDistanceWeight_continuous axis n j k

theorem graphSourceWeight_norm_le (distance plus : Bool) (axis : ℝ) (n j k : ℕ)
    (p : UnitCircle × UnitCircle) : ‖graphSourceWeight distance plus axis n j k p‖ ≤ 1 := by
  cases distance
  · exact graphProductWeight_norm_le plus n j k p
  · exact graphRotatedDistanceWeight_norm_le axis n j k p

theorem graphSourceWeight_parameter (distance plus : Bool) (axis : ℝ) (n j k : ℕ)
    (φ z : ℝ)
    (h : graphSourceWeight distance plus axis n j k
      (sourceUnitDirection (φ+Real.arctan z),
        sourceUnitDirection (φ-Real.arctan z+graphSourceChartAxis distance plus)) ≠ 0) :
    |z| ≤ 4 := by
  cases distance
  · exact graphProductWeight_parameter plus n j k φ z h
  · apply graphRotatedDistanceWeight_parameter axis n j k φ z
    simpa only [graphSourceWeight, graphSourceChartAxis, ↓reduceIte, add_zero] using h

end PlanarFalconer

end OAI
