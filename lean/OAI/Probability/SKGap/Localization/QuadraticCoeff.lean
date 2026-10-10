import Mathlib
import OAI.Probability.SKGap.Matrix.MatrixCoordinates

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace SKGap
section GaussianQuadratic
variable {ι : Type*} [Fintype ι]

def quadraticCoeff (r : ℝ) (w : EuclideanSpace ℝ ι) : MatrixCoordinates ι → ℝ
  | Sum.inl (i, k) => Real.sqrt (2 * r) * w i * w k
  | Sum.inr _ => 0

def linearCoeff (r : ℝ) (w : EuclideanSpace ℝ ι) : MatrixCoordinates ι → ℝ
  | Sum.inl _ => 0
  | Sum.inr i => 2 * Real.sqrt r * ‖w‖ * w i

lemma sum_coord_sq (w : EuclideanSpace ℝ ι) : ∑ i, (w i)^2 = ‖w‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]

lemma sum_outer_sq (w v : ι → ℝ) :
    (∑ i, ∑ k, (w i * w k - v i * v k)^2) =
      (∑ i, w i ^ 2)^2 + (∑ i, v i ^ 2)^2 - 2 * (∑ i, w i * v i)^2 := by
  simp_rw [show ∀ i k, (w i * w k - v i * v k)^2 =
    w i ^ 2 * w k ^ 2 + v i ^ 2 * v k ^ 2 - 2 * (w i * v i) * (w k * v k) by
      intros; ring]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul]
  ring

lemma quadraticCoeff_increment (r : ℝ) (hr : 0 ≤ r) (w v : EuclideanSpace ℝ ι) :
    (∑ k, (quadraticCoeff r w k - quadraticCoeff r v k)^2) =
      2 * r * (‖w‖^4 + ‖v‖^4 - 2 * (∑ i, w i * v i)^2) := by
  rw [Fintype.sum_sum_type]
  simp only [quadraticCoeff, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    Finset.sum_const_zero, add_zero, Fintype.sum_prod_type]
  simp_rw [show ∀ i k, (Real.sqrt (2*r) * w i * w k -
      Real.sqrt (2*r) * v i * v k)^2 = 2*r*(w i*w k-v i*v k)^2 by
    intro i k
    calc
      _ = (Real.sqrt (2*r))^2 * (w i*w k-v i*v k)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt (by positivity)]]
  simp_rw [← Finset.mul_sum]
  rw [sum_outer_sq, sum_coord_sq, sum_coord_sq]
  ring

lemma linearCoeff_increment (r : ℝ) (hr : 0 ≤ r) (w v : EuclideanSpace ℝ ι) :
    (∑ k, (linearCoeff r w k - linearCoeff r v k)^2) =
      4 * r * (‖w‖^4 + ‖v‖^4 - 2 * ‖w‖ * ‖v‖ * (∑ i, w i * v i)) := by
  rw [Fintype.sum_sum_type]
  simp only [linearCoeff, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    Finset.sum_const_zero, zero_add]
  simp_rw [show ∀ i, (2 * Real.sqrt r * ‖w‖ * w i -
      2 * Real.sqrt r * ‖v‖ * v i)^2 =
      4*r*(‖w‖^2*(w i)^2 + ‖v‖^2*(v i)^2 - 2*‖w‖*‖v‖*(w i*v i)) by
    intro i
    calc
      _ = 4*(Real.sqrt r)^2*(‖w‖^2*(w i)^2 + ‖v‖^2*(v i)^2 -
          2*‖w‖*‖v‖*(w i*v i)) := by ring
      _ = _ := by rw [Real.sq_sqrt hr]]
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [sum_coord_sq]
  ring

theorem quadratic_linear_increment_difference (r : ℝ) (hr : 0 ≤ r)
    (w v : EuclideanSpace ℝ ι) :
    (∑ k, (linearCoeff r w k - linearCoeff r v k)^2) -
      (∑ k, (quadraticCoeff r w k - quadraticCoeff r v k)^2) =
      2*r*((‖w‖^2 - ‖v‖^2)^2 +
        2*(‖w‖*‖v‖ - ∑ i, w i*v i)^2) := by
  rw [linearCoeff_increment r hr, quadraticCoeff_increment r hr]
  ring

theorem quadratic_linear_increment_le (r : ℝ) (hr : 0 ≤ r)
    (w v : EuclideanSpace ℝ ι) :
    (∑ k, (quadraticCoeff r w k - quadraticCoeff r v k)^2) ≤
      ∑ k, (linearCoeff r w k - linearCoeff r v k)^2 := by
  have h := quadratic_linear_increment_difference r hr w v
  have : 0 ≤ 2*r*((‖w‖^2 - ‖v‖^2)^2 +
      2*(‖w‖*‖v‖ - ∑ i, w i*v i)^2) := by positivity
  linarith

lemma quadratic_linear_orthogonal (r : ℝ) (w v : EuclideanSpace ℝ ι) :
    ∑ k, (linearCoeff r w k - linearCoeff r v k) *
      (quadraticCoeff r w k - quadraticCoeff r v k) = 0 := by
  rw [Fintype.sum_sum_type]
  simp only [linearCoeff, quadraticCoeff, sub_self, zero_mul, mul_zero,
    Finset.sum_const_zero, add_zero]

omit [Fintype ι] in
lemma continuous_quadraticCoeff (r : ℝ) : Continuous (quadraticCoeff (ι := ι) r) := by
  apply continuous_pi
  intro k
  cases k with
  | inl ik =>
    exact ((continuous_const.mul (PiLp.continuous_apply 2 (fun _ : ι => ℝ) ik.1)).mul
      (PiLp.continuous_apply 2 (fun _ : ι => ℝ) ik.2))
  | inr i => exact continuous_const

lemma continuous_linearCoeff (r : ℝ) : Continuous (linearCoeff (ι := ι) r) := by
  apply continuous_pi
  intro k
  cases k with
  | inl ik => exact continuous_const
  | inr i => exact (continuous_const.mul continuous_norm).mul (PiLp.continuous_apply 2 (fun _ : ι => ℝ) i)

end GaussianQuadratic
end SKGap

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
