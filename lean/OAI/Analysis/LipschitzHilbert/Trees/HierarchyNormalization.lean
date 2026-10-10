import OAI.Analysis.LipschitzHilbert.Phase.PhaseSelection

namespace OAI

/-!
# The normalized child identity

Exact algebra for §8, equation (src-25): the ratio of the parent amount
(with the residual omitted) to its child denominator equals the weighted
prediction ratio. No estimates or hierarchy hypotheses enter this identity.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem child_normalization_coefficient {n m μ : ℝ} (hn : 0 < n) (hm : 0 < m) :
    (m / n) ^ (1 - μ) * m ^ (μ - 1) = n ^ (μ - 1) := by
  rw [Real.div_rpow hm.le hn.le]
  have hm' : m ^ (1 - μ) * m ^ (μ - 1) = 1 := by
    rw [← Real.rpow_add hm, show (1 - μ) + (μ - 1) = 0 by ring, Real.rpow_zero]
  have hn' : (n ^ (1 - μ))⁻¹ = n ^ (μ - 1) := by
    rw [← Real.rpow_neg hn.le]
    congr 1
    ring
  calc
    _ = (m ^ (1 - μ) * m ^ (μ - 1)) * (n ^ (1 - μ))⁻¹ := by ring
    _ = _ := by rw [hm', one_mul, hn']

theorem normalized_child_sum (n : ℝ) (m : ι → ℝ) (A : ι → E) (lambda : ι → ℂ)
    (μ : ℝ) (hn : 0 < n) (hm : ∀ i, 0 < m i) :
    (∑ i, ((((m i / n) ^ (1 - μ) : ℝ) : ℂ) * lambda i) •
      (((m i ^ (μ - 1) : ℝ) : ℂ) • A i)) =
      ((n ^ (μ - 1) : ℝ) : ℂ) • ∑ i, lambda i • A i := by
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [smul_smul]
  congr 1
  have hc := congrArg (fun r : ℝ => (r : ℂ)) (child_normalization_coefficient hn (hm i) (μ := μ))
  push_cast at hc
  calc
    _ = (((((m i / n) ^ (1 - μ) : ℝ) : ℂ) * ((m i ^ (μ - 1) : ℝ) : ℂ))) * lambda i := by ring
    _ = _ := by rw [hc]

theorem normalized_vector_power (m : ℝ) (A : E) (μ p : ℝ) (hm : 0 < m) :
    ‖((m ^ (μ - 1) : ℝ) : ℂ) • A‖ ^ p = m ^ ((μ - 1) * p) * ‖A‖ ^ p := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hm.le _),
    Real.mul_rpow (Real.rpow_nonneg hm.le _) (norm_nonneg _), ← Real.rpow_mul hm.le]

/-- Equation (src-25), with every scalar power and normalization explicit. -/
theorem normalized_child_ratio (n : ℝ) (m : ι → ℝ) (A : ι → E) (lambda : ι → ℂ)
    (μ α p : ℝ) (hn : 0 < n) (hm : ∀ i, 0 < m i) (hrelation : p * μ = α - 1) :
    (n + n ^ (α - p) * ‖∑ i, lambda i • A i‖ ^ p) /
      (n + ∑ i, m i ^ (α - p) * ‖A i‖ ^ p) =
    (1 + ‖∑ i, ((((m i / n) ^ (1 - μ) : ℝ) : ℂ) * lambda i) •
      (((m i ^ (μ - 1) : ℝ) : ℂ) • A i)‖ ^ p) /
      (1 + ∑ i, (m i / n) * ‖((m i ^ (μ - 1) : ℝ) : ℂ) • A i‖ ^ p) := by
  have hexp : 1 + (μ - 1) * p = α - p := by nlinarith
  have hnum : n * (1 + ‖∑ i, ((((m i / n) ^ (1 - μ) : ℝ) : ℂ) * lambda i) •
      (((m i ^ (μ - 1) : ℝ) : ℂ) • A i)‖ ^ p) =
      n + n ^ (α - p) * ‖∑ i, lambda i • A i‖ ^ p := by
    rw [normalized_child_sum n m A lambda μ hn hm, normalized_vector_power n _ μ p hn]
    have hpow : n * n ^ ((μ - 1) * p) = n ^ (α - p) := by
      calc
        _ = n ^ (1 : ℝ) * n ^ ((μ - 1) * p) := by rw [Real.rpow_one]
        _ = n ^ (1 + (μ - 1) * p) := (Real.rpow_add hn _ _).symm
        _ = _ := by rw [hexp]
    calc
      _ = n + (n * n ^ ((μ - 1) * p)) * ‖∑ i, lambda i • A i‖ ^ p := by ring
      _ = _ := by rw [hpow]
  have hden : n * (1 + ∑ i, (m i / n) * ‖((m i ^ (μ - 1) : ℝ) : ℂ) • A i‖ ^ p) =
      n + ∑ i, m i ^ (α - p) * ‖A i‖ ^ p := by
    rw [mul_add, mul_one, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [normalized_vector_power (m i) (A i) μ p (hm i)]
    have hpow : m i * m i ^ ((μ - 1) * p) = m i ^ (α - p) := by
      calc
        _ = m i ^ (1 : ℝ) * m i ^ ((μ - 1) * p) := by rw [Real.rpow_one]
        _ = m i ^ (1 + (μ - 1) * p) := (Real.rpow_add (hm i) _ _).symm
        _ = _ := by rw [hexp]
    calc
      _ = (m i * m i ^ ((μ - 1) * p)) * ‖A i‖ ^ p := by field_simp
      _ = _ := by rw [hpow]
  rw [← hnum, ← hden]
  exact mul_div_mul_left _ _ hn.ne'

end LipschitzHilbert

end

end OAI
