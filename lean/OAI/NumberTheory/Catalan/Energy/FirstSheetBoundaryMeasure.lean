import Mathlib.MeasureTheory.Group.Circle
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic.Positivity

namespace OAI


noncomputable section

namespace InternalCatalan

open Complex Metric MeasureTheory

def firstSheetAngleMeasure : Measure ℝ :=
  volume.restrict (Set.Ioc 0 (2 * Real.pi))

instance firstSheetAngleMeasure_finite : IsFiniteMeasure firstSheetAngleMeasure := by
  unfold firstSheetAngleMeasure
  apply isFiniteMeasure_restrict.mpr
  rw [Real.volume_Ioc]
  exact ENNReal.ofReal_ne_top

def firstSheetBoundaryScale : NNReal := ⟨(2 * Real.pi)⁻¹, by positivity⟩

def firstSheetBoundaryMeasure : Measure Circle :=
  firstSheetBoundaryScale •
    Measure.map (Circle.exp : ℝ → Circle) firstSheetAngleMeasure

instance firstSheetBoundaryMeasure_finite : IsFiniteMeasure firstSheetBoundaryMeasure := by
  unfold firstSheetBoundaryMeasure
  infer_instance

def firstSheetBoundaryFunction {E : Type*} [TopologicalSpace E]
    (u : ℂ → E) (hu : ContinuousOn u (closedBall (0 : ℂ) 1)) : C(Circle, E) where
  toFun z := u (z : ℂ)
  continuous_toFun := hu.comp_continuous continuous_subtype_val (by
    intro z
    simp only [mem_closedBall, dist_zero_right, Circle.norm_coe, le_refl])

@[simp] theorem firstSheetBoundaryFunction_apply {E : Type*} [TopologicalSpace E]
    (u : ℂ → E) (hu : ContinuousOn u (closedBall (0 : ℂ) 1)) (z : Circle) :
    firstSheetBoundaryFunction u hu z = u (z : ℂ) := rfl

theorem firstSheetBoundary_integral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology E] {u : ℂ → E}
    (hu : ContinuousOn u (closedBall (0 : ℂ) 1)) :
    (∫ z : Circle, u (z : ℂ) ∂firstSheetBoundaryMeasure) =
      Real.circleAverage u 0 1 := by
  have hc : Continuous (fun z : Circle => u (z : ℂ)) :=
    (firstSheetBoundaryFunction u hu).continuous
  unfold firstSheetBoundaryMeasure
  rw [integral_smul_nnreal_measure,
    integral_map_of_stronglyMeasurable Circle.exp.continuous.measurable hc.stronglyMeasurable]
  change (2 * Real.pi)⁻¹ •
      (∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi), u (Circle.exp θ : ℂ)) = _
  rw [← intervalIntegral.integral_of_le Real.two_pi_pos.le]
  simp only [Real.circleAverage_def, Circle.coe_exp, circleMap, ofReal_one,
    one_mul, zero_add]

theorem firstSheetBoundaryMeasure_mass : firstSheetBoundaryMeasure Set.univ = 1 := by
  have h := firstSheetBoundary_integral
    (u := fun _ : ℂ => (1 : ℝ)) continuousOn_const
  have hreal : firstSheetBoundaryMeasure.real Set.univ = 1 := by
    simpa only [integral_const, smul_eq_mul, mul_one, Real.circleAverage_const] using h
  exact (isProbabilityMeasure_iff_real.mpr hreal).measure_univ

instance firstSheetBoundaryMeasure_probability :
    IsProbabilityMeasure firstSheetBoundaryMeasure := ⟨firstSheetBoundaryMeasure_mass⟩

end InternalCatalan

end

end OAI
