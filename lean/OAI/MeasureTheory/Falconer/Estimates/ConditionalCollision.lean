import OAI.MeasureTheory.Falconer.Geometry.ProjectionLaw
import Mathlib.Probability.ConditionalProbability

namespace OAI

/-! # Returning full-conditional projection tests to the original cell law -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem conditional_product_mass_reconstruct (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (Q : Set (Space d)) (hQ : μ Q ≠ 0) (A : Set (Space d × Space d)) :
    (μ Q)^2 * ((ProbabilityTheory.cond μ Q).prod (ProbabilityTheory.cond μ Q)) A =
      ((μ.restrict Q).prod (μ.restrict Q)) A := by
  rw [ProbabilityTheory.cond,Measure.prod_smul_left,Measure.prod_smul_right,
    Measure.smul_apply,Measure.smul_apply,smul_eq_mul,smul_eq_mul]
  calc
    _ = (μ Q*(μ Q)⁻¹)*(μ Q*(μ Q)⁻¹)*
        ((μ.restrict Q).prod (μ.restrict Q)) A := by ring
    _ = _ := by rw [ENNReal.mul_inv_cancel hQ (measure_ne_top μ Q)]; simp

theorem conditional_projection_to_restriction (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (Q : Set (Space d)) (hQ : μ Q ≠ 0) (w : Space d) (W : ℝ) {F : ℝ≥0∞}
    (h : projectionCollision (ProbabilityTheory.cond μ Q) w W ≤ F) :
    ((μ.restrict Q).prod (μ.restrict Q))
      {z : Space d × Space d | |inner ℝ w (z.1-z.2)| ≤ W} ≤ F*(μ Q)^2 := by
  rw [← conditional_product_mass_reconstruct μ Q hQ, mul_comm F]
  apply mul_le_mul' le_rfl
  simpa only [projectionCollision,real_inner_comm w] using h

end Falconer

end OAI
