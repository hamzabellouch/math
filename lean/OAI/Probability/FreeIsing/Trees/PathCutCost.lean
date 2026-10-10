import OAI.Probability.FreeIsing.Energy.Attenuation

namespace OAI

noncomputable section

namespace Problem367
namespace PathCutCost

theorem abs_sub_le_geometric
    {x y : ℕ → ℝ} {q B : ℝ} (hq : 0 ≤ q)
    (hzero : |x 0 - y 0| ≤ B)
    (hstep : ∀ n, |x (n + 1) - y (n + 1)| ≤ q * |x n - y n|) :
    ∀ n, |x n - y n| ≤ B * q ^ n := by
  intro n
  induction n with
  | zero => simpa using hzero
  | succ n ih =>
    calc
      |x (n + 1) - y (n + 1)| ≤ q * |x n - y n| := hstep n
      _ ≤ q * (B * q ^ n) := mul_le_mul_of_nonneg_left ih hq
      _ = B * q ^ (n + 1) := by rw [pow_succ]; ring

theorem sum_abs_sub_le
    {x y : ℕ → ℝ} {q B : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (hzero : |x 0 - y 0| ≤ B)
    (hstep : ∀ n, |x (n + 1) - y (n + 1)| ≤ q * |x n - y n|) (n : ℕ) :
    (∑ i ∈ Finset.range n, |x i - y i|) ≤ B / (1 - q) := by
  have hB : 0 ≤ B := (abs_nonneg _).trans hzero
  have hgeom : (∑ i ∈ Finset.range n, q ^ i) ≤ 1 / (1 - q) := by
    apply (le_div_iff₀ (sub_pos.mpr hq1)).mpr
    rw [geom_sum_mul_of_le_one hq1.le]
    exact sub_le_self _ (pow_nonneg hq n)
  calc
    (∑ i ∈ Finset.range n, |x i - y i|) ≤ ∑ i ∈ Finset.range n, B * q ^ i :=
      Finset.sum_le_sum (fun i _ => abs_sub_le_geometric hq hzero hstep i)
    _ = B * ∑ i ∈ Finset.range n, q ^ i := (Finset.mul_sum ..).symm
    _ ≤ B * (1 / (1 - q)) := mul_le_mul_of_nonneg_left hgeom hB
    _ = B / (1 - q) := by ring

theorem abs_log_prod_sq_ratio_le {ι : Type*} (s : Finset ι)
    {a b : ι → ℝ} (ha : ∀ i ∈ s, 0 < a i) (hb : ∀ i ∈ s, 0 < b i) :
    |Real.log ((∏ i ∈ s, a i ^ 2) / (∏ i ∈ s, b i ^ 2))| ≤
      2 * ∑ i ∈ s, |Real.log (a i) - Real.log (b i)| := by
  have hA : (∏ i ∈ s, a i ^ 2) ≠ 0 :=
    ne_of_gt (Finset.prod_pos (fun i hi => pow_pos (ha i hi) _))
  have hB : (∏ i ∈ s, b i ^ 2) ≠ 0 :=
    ne_of_gt (Finset.prod_pos (fun i hi => pow_pos (hb i hi) _))
  have hlog : Real.log ((∏ i ∈ s, a i ^ 2) / (∏ i ∈ s, b i ^ 2)) =
      2 * ∑ i ∈ s, (Real.log (a i) - Real.log (b i)) := by
    rw [Real.log_div hA hB,
      Real.log_prod (fun i hi => pow_ne_zero _ (ha i hi).ne'),
      Real.log_prod (fun i hi => pow_ne_zero _ (hb i hi).ne')]
    simp_rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hlog, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)

theorem abs_log_attenuation_prod_ratio_le
    {x y : ℕ → ℝ} {theta q B : ℝ} (htheta : theta ^ 2 ≤ 1)
    (hq : 0 ≤ q) (hq1 : q < 1)
    (hzero : |x 0 - y 0| ≤ B)
    (hstep : ∀ i, |x (i + 1) - y (i + 1)| ≤ q * |x i - y i|) (n : ℕ) :
    |Real.log ((∏ i ∈ Finset.range n, responseAttenuation theta (x i) ^ 2) /
      (∏ i ∈ Finset.range n, responseAttenuation theta (y i) ^ 2))| ≤
      4 * B / (1 - q) := by
  have hloglip : ∀ i, |Real.log (responseAttenuation theta (x i)) -
      Real.log (responseAttenuation theta (y i))| ≤ 2 * |x i - y i| := by
    intro i
    simpa only [Real.dist_eq, NNReal.coe_ofNat] using
      (lipschitzWith_log_responseAttenuation htheta).dist_le_mul (x i) (y i)
  calc
    _ ≤ 2 * ∑ i ∈ Finset.range n,
        |Real.log (responseAttenuation theta (x i)) -
          Real.log (responseAttenuation theta (y i))| :=
      abs_log_prod_sq_ratio_le _ (fun i _ => responseAttenuation_pos htheta (x i))
        (fun i _ => responseAttenuation_pos htheta (y i))
    _ ≤ 2 * ∑ i ∈ Finset.range n, 2 * |x i - y i| :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hloglip i)) (by norm_num)
    _ = 4 * ∑ i ∈ Finset.range n, |x i - y i| := by rw [← Finset.mul_sum]; ring
    _ ≤ 4 * (B / (1 - q)) :=
      mul_le_mul_of_nonneg_left (sum_abs_sub_le hq hq1 hzero hstep n) (by norm_num)
    _ = 4 * B / (1 - q) := by ring

theorem attenuation_prod_le_exp_mul
    {x y : ℕ → ℝ} {theta q B : ℝ} (htheta : theta ^ 2 ≤ 1)
    (hq : 0 ≤ q) (hq1 : q < 1)
    (hzero : |x 0 - y 0| ≤ B)
    (hstep : ∀ i, |x (i + 1) - y (i + 1)| ≤ q * |x i - y i|) (n : ℕ) :
    (∏ i ∈ Finset.range n, responseAttenuation theta (x i) ^ 2) ≤
      Real.exp (4 * B / (1 - q)) *
        (∏ i ∈ Finset.range n, responseAttenuation theta (y i) ^ 2) := by
  have hA : 0 < ∏ i ∈ Finset.range n, responseAttenuation theta (x i) ^ 2 :=
    Finset.prod_pos (fun i _ => pow_pos (responseAttenuation_pos htheta (x i)) _)
  have hB : 0 < ∏ i ∈ Finset.range n, responseAttenuation theta (y i) ^ 2 :=
    Finset.prod_pos (fun i _ => pow_pos (responseAttenuation_pos htheta (y i)) _)
  apply (div_le_iff₀ hB).mp
  apply (Real.log_le_iff_le_exp (div_pos hA hB)).mp
  exact (le_abs_self _).trans (abs_log_attenuation_prod_ratio_le htheta hq hq1 hzero hstep n)

theorem attenuation_prod_le_exp_mul_of_recursion
    {x y side : ℕ → ℝ} {ψ : ℝ → ℝ} {theta q B : ℝ}
    (htheta : theta ^ 2 ≤ 1) (hq : 0 ≤ q) (hq1 : q < 1)
    (hψ : LipschitzWith ⟨q, hq⟩ ψ)
    (hx : ∀ i, x (i + 1) = side i + ψ (x i))
    (hy : ∀ i, y (i + 1) = side i + ψ (y i))
    (hzero : |x 0 - y 0| ≤ B) (n : ℕ) :
    (∏ i ∈ Finset.range n, responseAttenuation theta (x i) ^ 2) ≤
      Real.exp (4 * B / (1 - q)) *
        (∏ i ∈ Finset.range n, responseAttenuation theta (y i) ^ 2) := by
  apply attenuation_prod_le_exp_mul htheta hq hq1 hzero ?_ n
  intro i
  rw [hx i, hy i]
  have h := hψ.dist_le_mul (x i) (y i)
  change |ψ (x i) - ψ (y i)| ≤ q * |x i - y i| at h
  simpa only [add_sub_add_left_eq_sub] using h

end PathCutCost
end Problem367

end

end OAI
