import OAI.Probability.FreeIsing.Trees.PathCutCost

namespace OAI

noncomputable section
namespace Problem367.PathCutCost

theorem attenuation_prod_le_exp_mul_of_finite_contraction
    {x y : ℕ → ℝ} {theta q B : ℝ} (n : ℕ)
    (htheta : theta ^ 2 ≤ 1) (hq : 0 ≤ q) (hq1 : q < 1)
    (hzero : |x 0 - y 0| ≤ B)
    (hstep : ∀ i, i + 1 < n →
      |x (i + 1) - y (i + 1)| ≤ q * |x i - y i|) :
    (∏ i ∈ Finset.range n, responseAttenuation theta (x i) ^ 2) ≤
      Real.exp (4 * B / (1 - q)) *
        (∏ i ∈ Finset.range n, responseAttenuation theta (y i) ^ 2) := by
  let X : ℕ → ℝ := fun i => if i < n then x i else 0
  let Y : ℕ → ℝ := fun i => if i < n then y i else 0
  have hB : 0 ≤ B := (abs_nonneg _).trans hzero
  have hzero' : |X 0 - Y 0| ≤ B := by
    by_cases hn : 0 < n
    · simpa only [X, Y, ite_eq_left hn] using hzero
    · simpa only [X, Y, ite_eq_right hn, sub_self, abs_zero] using hB
  have hstep' : ∀ i, |X (i + 1) - Y (i + 1)| ≤ q * |X i - Y i| := by
    intro i
    by_cases hi : i + 1 < n
    · have hi' : i < n := by omega
      simpa only [X, Y, ite_eq_left hi, ite_eq_left hi'] using hstep i hi
    · simp only [X, Y, ite_eq_right hi, sub_self, abs_zero]
      exact mul_nonneg hq (abs_nonneg _)
  have h := attenuation_prod_le_exp_mul htheta hq hq1 hzero' hstep' n
  have hx : (∏ i ∈ Finset.range n, responseAttenuation theta (X i) ^ 2) =
      ∏ i ∈ Finset.range n, responseAttenuation theta (x i) ^ 2 := by
    apply Finset.prod_congr rfl
    intro i hi
    simp only [X, ite_eq_left (Finset.mem_range.mp hi)]
  have hy : (∏ i ∈ Finset.range n, responseAttenuation theta (Y i) ^ 2) =
      ∏ i ∈ Finset.range n, responseAttenuation theta (y i) ^ 2 := by
    apply Finset.prod_congr rfl
    intro i hi
    simp only [Y, ite_eq_left (Finset.mem_range.mp hi)]
  rw [hx, hy] at h
  exact h

theorem attenuation_prod_le_exp_mul_of_finite_recursion
    {x y side : ℕ → ℝ} {ψ : ℝ → ℝ} {theta q B : ℝ} (n : ℕ)
    (htheta : theta ^ 2 ≤ 1) (hq : 0 ≤ q) (hq1 : q < 1)
    (hψ : LipschitzWith ⟨q, hq⟩ ψ)
    (hx : ∀ i, i + 1 < n → x (i + 1) = side i + ψ (x i))
    (hy : ∀ i, i + 1 < n → y (i + 1) = side i + ψ (y i))
    (hzero : |x 0 - y 0| ≤ B) :
    (∏ i ∈ Finset.range n, responseAttenuation theta (x i) ^ 2) ≤
      Real.exp (4 * B / (1 - q)) *
        (∏ i ∈ Finset.range n, responseAttenuation theta (y i) ^ 2) := by
  apply attenuation_prod_le_exp_mul_of_finite_contraction n htheta hq hq1 hzero
  intro i hi
  rw [hx i hi, hy i hi]
  have h := hψ.dist_le_mul (x i) (y i)
  change |ψ (x i) - ψ (y i)| ≤ q * |x i - y i| at h
  simpa only [add_sub_add_left_eq_sub] using h

end Problem367.PathCutCost

end

end OAI
