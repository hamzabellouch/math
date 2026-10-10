import OAI.Probability.InvariantIsing.Cavity.CavityBlockFactor
import OAI.Probability.InvariantIsing.Cavity.CavityCappedLog

namespace OAI

/-! A quadratic growth bound for the actual cavity exponent. The bound
does not require the special-coordinate block matrices to commute. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def cavityMatrixMass {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, |A i j|

lemma cavityMatrixMass_nonneg {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) :
    0 ≤ cavityMatrixMass A := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))

lemma cavity_bilinear_abs_bound {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ)
    (x : Fin d → ℝ) (y : Fin n → ℝ) {a b : ℝ} (ha : 0 ≤ a) (_hb : 0 ≤ b)
    (hx : ∀ i, |x i| ≤ a) (hy : ∀ j, |y j| ≤ b) :
    |∑ i, ∑ j, x i * A i j * y j| ≤ cavityMatrixMass A * (a * b) := by
  calc
    _ ≤ ∑ i, |∑ j, x i * A i j * y j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |x i * A i j * y j| :=
      Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, |A i j| * (a * b) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      calc
        _ = |A i j| * (|x i| * |y j|) := by simp only [abs_mul]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul (hx i) (hy j) (abs_nonneg _) ha)
          (abs_nonneg _)
    _ = _ := by simp only [cavityMatrixMass, Finset.sum_mul]

lemma cavity_quadratic_abs_bound {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (y : EuclideanSpace ℝ (Fin d)) :
    |cavityQuadratic A y| ≤ cavityMatrixMass A * ‖y‖ ^ 2 := by
  have hy i : |y i| ≤ ‖y‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le y i
  have h := cavity_bilinear_abs_bound A y y (norm_nonneg y) (norm_nonneg y) hy hy
  have hm := cavityMatrixMass_nonneg A
  rw [cavityQuadratic, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  nlinarith [sq_nonneg ‖y‖]

lemma cavity_spin_quadratic_abs_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (ε : Spin n) :
    |cavityQuadratic A (fun j => spinValue (ε j))| ≤ cavityMatrixMass A := by
  have h := cavity_bilinear_abs_bound A (fun j => spinValue (ε j)) (fun j => spinValue (ε j))
    zero_le_one zero_le_one (fun i => (abs_spinValue (ε i)).le) (fun i => (abs_spinValue (ε i)).le)
  rw [cavityQuadratic, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hm := cavityMatrixMass_nonneg A
  simp only [mul_one] at h
  linarith

theorem cavity_logFactor_growth {d n : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (y : EuclideanSpace ℝ (Fin d)) (ε : Spin n) :
    |cavityLogFactor K L C y ε| ≤
      (cavityMatrixMass K + cavityMatrixMass L + cavityMatrixMass C) * (1 + ‖y‖ ^ 2) := by
  have hK := cavity_quadratic_abs_bound K y
  have hC := cavity_spin_quadratic_abs_bound C ε
  have hy i : |y i| ≤ ‖y‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le y i
  have hL := cavity_bilinear_abs_bound L y (fun j => spinValue (ε j))
    (norm_nonneg y) zero_le_one hy (fun j => (abs_spinValue (ε j)).le)
  have hnorm : ‖y‖ ≤ 1 + ‖y‖ ^ 2 := by nlinarith [sq_nonneg (‖y‖ - 1)]
  have hL' := mul_le_mul_of_nonneg_left hnorm (cavityMatrixMass_nonneg L)
  have hsum := (abs_add_le (cavityQuadratic K y + ∑ i, ∑ j, y i * L i j * spinValue (ε j))
    (cavityQuadratic C (fun j => spinValue (ε j)))).trans
      (add_le_add (abs_add_le _ _) le_rfl)
  change |cavityLogFactor K L C y ε| ≤ _ at hsum
  simp only [mul_one] at hL
  nlinarith [cavityMatrixMass_nonneg K, cavityMatrixMass_nonneg C,
    mul_nonneg (cavityMatrixMass_nonneg C) (sq_nonneg ‖y‖)]

end InvariantIsing

end

end OAI
