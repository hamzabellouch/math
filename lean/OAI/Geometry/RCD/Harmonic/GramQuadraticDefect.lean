import OAI.Geometry.RCD.Harmonic.GramTraceDefect
import OAI.Geometry.RCD.Coordinates.FrameResidualEnergy
import OAI.Geometry.RCD.Harmonic.GramDefect

namespace OAI

/-! # Quadratic-form error from the same finite Gram defect -/

open Set Finset Filter MeasureTheory
open scoped InnerProductSpace
noncomputable section
namespace RegularPointCoordinates

theorem matrix_gram_quadratic_defect {n : ℕ} (G : Fin n → Fin n → ℝ) (a : Euclidean n) :
    |(∑ i, ∑ j, a i*a j*G i j)-‖a‖^2|≤ matrixGramDefect G*‖a‖^2 := by
  classical
  have hid : (∑ i, ∑ j, a i*a j*(if i=j then (1:ℝ) else 0))=‖a‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [mul_ite,pow_two]
  have he : (∑ i, ∑ j, a i*a j*G i j)-‖a‖^2=
      ∑ i, ∑ j, a i*a j*(G i j-(if i=j then 1 else 0)) := by
    simp only [mul_sub,sum_sub_distrib,hid]
  have ha (i : Fin n) : |a i|≤‖a‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le a i
  have hp (i j : Fin n) : |a i*a j|≤‖a‖^2 := by
    rw [abs_mul,pow_two]
    exact mul_le_mul (ha i) (ha j) (abs_nonneg _) (norm_nonneg _)
  rw [he]
  calc
    _≤∑ i, |∑ j, a i*a j*(G i j-(if i=j then 1 else 0))| := abs_sum_le_sum_abs _ _
    _≤∑ i, ∑ j, |a i*a j*(G i j-(if i=j then 1 else 0))| :=
      sum_le_sum (fun _ _ => abs_sum_le_sum_abs _ _)
    _≤∑ i, ∑ j, ‖a‖^2*|G i j-(if i=j then 1 else 0)| := by
      apply sum_le_sum
      intro i _
      apply sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hp i j) (abs_nonneg _)
    _=matrixGramDefect G*‖a‖^2 := by
      rw [mul_comm (matrixGramDefect G) (‖a‖^2)]
      simp only [matrixGramDefect,mul_sum]

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem localGamma_column_defect {n : ℕ} (u : Fin n → SobolevSpace μ hQ) (a : Euclidean n) :
    ∀ᵐ x ∂μ, |localGamma μ hQ (sobolevColumnMap μ hQ u a)
      (sobolevColumnMap μ hQ u a) x-‖a‖^2|≤gramDefect μ hQ u x*‖a‖^2 := by
  filter_upwards [localGamma_column_pair μ hQ u a a] with x hx
  rw [hx]
  exact matrix_gram_quadratic_defect (fun i j => localGamma μ hQ (u i) (u j) x) a

end RegularPointCoordinates

end

end OAI
