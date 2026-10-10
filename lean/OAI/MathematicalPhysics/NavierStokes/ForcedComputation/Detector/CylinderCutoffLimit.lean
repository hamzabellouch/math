import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CylinderLocalEnergyInput
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneCutoffLimit

namespace OAI

/-! Squared compact cutoffs recover every integrable quantity on the
mixed domain by dominated convergence. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows ExpandingDetector MeasureTheory Set Filter
open scoped Topology

theorem cylinderWeight_range (n : ℕ) (x : Plane) : cylinderWeight n x ∈ Icc (0 : ℝ) 1 := by
  have h := concentrationCutoff_range ((n : ℝ)+1) (0 : Plane) x
  unfold cylinderWeight
  constructor
  · positivity
  · nlinarith [h.1, h.2, sq_nonneg (1-concentrationCutoff ((n : ℝ)+1) 0 x)]

theorem cylinderWeight_continuous (n : ℕ) : Continuous (cylinderWeight n) :=
  ((concentrationCutoff_smooth ((n : ℝ)+1) (0 : Plane)).pow 2).continuous

theorem cylinderWeight_tendsto_one (x : Plane) :
    Tendsto (fun n : ℕ => cylinderWeight n x) atTop (𝓝 1) := by
  simpa only [cylinderWeight, one_pow] using (concentrationCutoff_tendsto_one 0 x).pow 2

theorem cylinderWeight_integrable_mul {f : Plane × ℝ → ℝ}
    (hf : Integrable f cylinderMeasure) (n : ℕ) :
    Integrable (fun y => cylinderWeight n y.1 * f y) cylinderMeasure := by
  apply hf.bdd_mul ((cylinderWeight_continuous n).comp continuous_fst).aestronglyMeasurable
  filter_upwards [] with y
  change |cylinderWeight n y.1| ≤ 1
  rw [abs_of_nonneg (cylinderWeight_range n y.1).1]
  exact (cylinderWeight_range n y.1).2

theorem cylinderWeight_integral_limit {f : Plane × ℝ → ℝ}
    (hf : Integrable f cylinderMeasure) :
    Tendsto (fun n : ℕ => ∫ y, cylinderWeight n y.1 * f y ∂cylinderMeasure)
      atTop (𝓝 (∫ y, f y ∂cylinderMeasure)) := by
  apply tendsto_integral_of_dominated_convergence (fun y => |f y|)
  · intro n
    exact ((cylinderWeight_continuous n).comp continuous_fst).aestronglyMeasurable.mul
      hf.aestronglyMeasurable
  · simpa only [Real.norm_eq_abs] using hf.norm
  · intro n
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (cylinderWeight_range n y.1).1]
    exact (mul_le_mul_of_nonneg_right (cylinderWeight_range n y.1).2 (abs_nonneg _)).trans_eq
      (one_mul _)
  · filter_upwards [] with y
    simpa only [one_mul] using (cylinderWeight_tendsto_one y.1).mul_const (f y)

end ForcedComputation.VelocityDetector

end

end OAI
