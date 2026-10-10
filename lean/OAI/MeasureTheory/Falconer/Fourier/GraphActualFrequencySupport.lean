import OAI.MeasureTheory.Falconer.Graphs.GraphInheritedTransformChart
import OAI.MeasureTheory.Falconer.Graphs.GraphAlgebraicDirections

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem graphSourceWeight_sqrt_bound (distance plus : Bool) (axis : ℝ) (n j k : ℕ)
    (φ z : ℝ)
    (h : graphSourceWeight distance plus axis n j k
      (sourceUnitDirection (φ+Real.arctan z),
        sourceUnitDirection (φ-Real.arctan z+graphSourceChartAxis distance plus)) ≠ 0) :
    Real.sqrt (1+z^2) ≤ 4 := by
  apply (graph_parameter_bound φ z _).1
  cases distance
  · cases plus
    · have hs : (sourceUnitDirection (φ+Real.arctan z),
          sourceUnitDirection (φ-Real.arctan z+Real.pi)) ∈ tsupport circleGraphSignMinus := by
        apply subset_closure
        intro hz
        exact h (by simp [graphSourceWeight, graphSourceChartAxis, graphProductWeight, hz])
      have hh := circleGraphSignMinus_tsupport hs
      change 1 ≤ ‖sourceDirection (φ+Real.arctan z)-sourceDirection (φ-Real.arctan z+Real.pi)‖ at hh
      rw [sourceDirection_add_pi, sub_neg_eq_add] at hh
      linarith
    · have hs : (sourceUnitDirection (φ+Real.arctan z),
          sourceUnitDirection (φ-Real.arctan z)) ∈ tsupport circleGraphSignPlus := by
        apply subset_closure
        intro hz
        exact h (by simp [graphSourceWeight, graphSourceChartAxis, graphProductWeight, hz])
      have hh := circleGraphSignPlus_tsupport hs
      change 1 ≤ ‖sourceDirection (φ+Real.arctan z)+sourceDirection (φ-Real.arctan z)‖ at hh
      linarith
  · have he : graphRotatedDistanceWeight axis n j k
        (sourceUnitDirection (φ+Real.arctan z), sourceUnitDirection (φ-Real.arctan z)) ≠ 0 := by
      simpa only [graphSourceWeight, graphSourceChartAxis, ↓reduceIte, add_zero] using h
    rw [graphRotatedDistanceWeight_eq] at he
    have hu : sourceConeCircle axis (sourceUnitDirection (φ+Real.arctan z)) ≠ 0 := by
      intro hz; exact he (by simp [hz])
    have hv : sourceConeCircle axis (sourceUnitDirection (φ-Real.arctan z)) ≠ 0 := by
      intro hz; exact he (by simp [hz])
    have hh := sourceConeCircle_plus_nondegenerate axis _ _ (subset_closure hu) (subset_closure hv)
    exact (by norm_num : (1/2:ℝ) ≤ 6/5).trans hh

theorem graphActualTransport_frequency_support
    (b : Fin 4 → Plane → UnitCircle → ℂ) (x : Fin 4 → Plane)
    (distance plus : Bool) (axis : ℝ) (n j k : ℕ)
    {Ψ : ℝ → ℝ} (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    (R : ℝ) (p : ℝ × Plane)
    (hp : graphTransport (graphFourKernel b (graphSourceWeight distance plus axis n j k) x)
      Ψ R (graphSourceChartAxis distance plus) p ≠ 0) :
    1/8 ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ 8 ∧ |p.1| ≤ 4 := by
  have hb : Ψ (‖p.2‖*Real.sqrt (1+p.1^2)/2) ≠ 0 := by
    intro hz; exact hp (by simp [graphTransport, hz])
  have hf : graphFourKernel b (graphSourceWeight distance plus axis n j k) x
      (R*(‖p.2‖*Real.sqrt (1+p.1^2)/2))
      (sourceUnitDirection (graphPlaneAngle p.2+Real.arctan p.1))
      (sourceUnitDirection (graphPlaneAngle p.2-Real.arctan p.1+graphSourceChartAxis distance plus)) ≠ 0 := by
    intro hz; exact hp (by simp [graphTransport, hz])
  have hw := graphFourKernel_weight_ne_zero b _ x _ _ _ hf
  have hs := graphSourceWeight_sqrt_bound distance plus axis n j k _ _ hw
  have hz := graphSourceWeight_parameter distance plus axis n j k _ _ hw
  have hr := hsupp _ hb
  have hlow : 1 ≤ Real.sqrt (1+p.1^2) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith [sq_nonneg p.1]
  refine ⟨?_,?_,hz⟩
  · nlinarith [hr.1, mul_le_mul_of_nonneg_left hs (norm_nonneg p.2)]
  · nlinarith [hr.2, mul_le_mul_of_nonneg_left hlow (norm_nonneg p.2)]

end PlanarFalconer

end OAI
