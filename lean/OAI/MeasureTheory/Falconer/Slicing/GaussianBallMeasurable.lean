import OAI.MeasureTheory.Falconer.Slicing.GaussianCloseMass
import OAI.MeasureTheory.Falconer.Slicing.GaussianPointClose

namespace OAI

/-! # Joint measurability of the ball tests used to prune Gaussian slices -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_direction_ball_mass_measurable (ν : Measure (Sphere d)) [SFinite ν] (r ρ : ℝ) :
    Measurable (fun p : (Fin h → Space d) × Sphere d =>
      gaussianDirectionSliceMeasure ν p.1 r (ball p.2 ρ)) := by
  simp only [gaussianDirectionSliceMeasure,Measure.smul_apply,smul_eq_mul,
    Measure.restrict_apply measurableSet_ball]
  apply Measurable.const_mul
  let S : Set (((Fin h → Space d) × Sphere d) × Sphere d) :=
    {p | dist p.2 p.1.2 < ρ ∧ ∀ i, |inner ℝ (p.2:Space d) (p.1.1 i)| ≤ r}
  have hS : MeasurableSet S := by
    simp only [S,ofPred_and,ofPred_forall]
    apply MeasurableSet.inter (measurableSet_lt (by fun_prop) measurable_const)
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (by fun_prop) measurable_const
  convert (measurable_measure_prodMk_left (ν := ν) hS) using 1
  ext p
  congr 1

theorem gaussian_point_ball_mass_measurable (μ : Measure (Space d)) [SFinite μ] (r ρ : ℝ) :
    Measurable (fun p : ((Fin h → Space d) × Space h) × Space d =>
      gaussianPointSliceMeasure μ p.1.1 p.1.2 r (ball p.2 ρ)) := by
  simp only [gaussianPointSliceMeasure,Measure.smul_apply,smul_eq_mul,
    Measure.restrict_apply measurableSet_ball]
  apply Measurable.const_mul
  let S : Set ((((Fin h → Space d) × Space h) × Space d) × Space d) :=
    {p | dist p.2 p.1.2 < ρ ∧ ∀ i, |inner ℝ p.2 (p.1.1.1 i)-p.1.1.2 i| ≤ r}
  have hS : MeasurableSet S := by
    simp only [S,ofPred_and,ofPred_forall]
    apply MeasurableSet.inter (measurableSet_lt (by fun_prop) measurable_const)
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (by fun_prop) measurable_const
  convert (measurable_measure_prodMk_left (ν := μ) hS) using 1
  ext p
  congr 1

end Falconer

end OAI
