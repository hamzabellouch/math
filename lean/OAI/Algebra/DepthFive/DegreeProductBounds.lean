import OAI.Algebra.DepthFive.DegreeDistances

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem335

lemma low_degree_power_saving {n s q : ℝ} (hn : 1 ≤ n) (hq : 0 ≤ q)
    (hq' : q ≤ n ^ (-(2 / 5 : ℝ))) (hs : Real.sqrt n / 2 ≤ s) :
    q ^ (s / 4) ≤ n ^ (-Real.sqrt n / 20) := by
  have hn0 : 0 ≤ n := by linarith
  have hs0 : 0 ≤ s := le_trans (by positivity) hs
  calc
    q ^ (s / 4) ≤ (n ^ (-(2 / 5 : ℝ))) ^ (s / 4) :=
      Real.rpow_le_rpow hq hq' (by positivity)
    _ = n ^ (-(s / 10)) := by rw [← Real.rpow_mul hn0]; congr 1; ring
    _ ≤ n ^ (-Real.sqrt n / 20) := by
      apply Real.rpow_le_rpow_of_exponent_le hn
      linarith

lemma high_degree_power_saving {n q lam t : ℝ} (hn : 1 ≤ n) (hq : 0 ≤ q)
    (hq' : q ≤ n ^ (-(2 / 5 : ℝ))) (hlam : 3 / 8 ≤ lam)
    (ht : Real.sqrt n / 4 ≤ t) :
    q ^ (lam * t / 2) ≤ n ^ (-(3 * Real.sqrt n / 160)) := by
  have hn0 : 0 ≤ n := by linarith
  have ht0 : 0 ≤ t := le_trans (by positivity) ht
  have hlam0 : 0 ≤ lam := by linarith
  have hprod : 3 / 8 * (Real.sqrt n / 4) ≤ lam * t :=
    mul_le_mul hlam ht (by positivity) hlam0
  calc
    q ^ (lam * t / 2) ≤ (n ^ (-(2 / 5 : ℝ))) ^ (lam * t / 2) :=
      Real.rpow_le_rpow hq hq' (by positivity)
    _ = n ^ (-(lam * t / 5)) := by rw [← Real.rpow_mul hn0]; congr 1; ring
    _ ≤ n ^ (-(3 * Real.sqrt n / 160)) := by
      apply Real.rpow_le_rpow_of_exponent_le hn
      nlinarith

lemma prod_exp_corrections {ι : Type*} (I : Finset ι) (H d E : ι → ℝ)
    {q B : ℝ} (hq : 0 ≤ q) (hH : ∀ i ∈ I, 0 ≤ H i)
    (hbound : ∀ i ∈ I, H i ≤ q ^ d i * Real.exp (E i))
    (hE : ∑ i ∈ I, E i ≤ B) :
    (∏ i ∈ I, H i) ≤ (∏ i ∈ I, q ^ d i) * Real.exp B := by
  calc
    (∏ i ∈ I, H i) ≤ ∏ i ∈ I, q ^ d i * Real.exp (E i) :=
      Finset.prod_le_prod₀ hH hbound
    _ = (∏ i ∈ I, q ^ d i) * Real.exp (∑ i ∈ I, E i) := by
      rw [Finset.prod_mul_distrib, Real.exp_sum]
    _ ≤ (∏ i ∈ I, q ^ d i) * Real.exp B := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hE)
      exact Finset.prod_nonneg (fun i _ => Real.rpow_nonneg hq (d i))

lemma all_low_degree_product_bound {ι : Type*} (I : Finset ι) (e : ι → ℕ)
    (H E : ι → ℝ) {n s q C : ℝ} (hn : 1 ≤ n) (hs : 0 < s)
    (hs' : Real.sqrt n / 2 ≤ s) (hq : 0 < q) (hq1 : q ≤ 1)
    (hq' : q ≤ n ^ (-(2 / 5 : ℝ)))
    (he : ∀ i ∈ I, 0 < e i) (he' : ∀ i ∈ I, (e i : ℝ) < n / (4 * s))
    (hsum : ∑ i ∈ I, (e i : ℝ) = n) (hH : ∀ i ∈ I, 0 ≤ H i)
    (hbound : ∀ i ∈ I, H i ≤ q ^ (degreeDistance n s (e i) / 2) * Real.exp (E i))
    (hE : ∑ i ∈ I, E i ≤ C * Real.sqrt n) :
    (∏ i ∈ I, H i) ≤ Real.exp (C * Real.sqrt n) * n ^ (-Real.sqrt n / 20) := by
  have hn0 : 0 < n := by linarith
  calc
    (∏ i ∈ I, H i) ≤ (∏ i ∈ I, q ^ (degreeDistance n s (e i) / 2)) *
        Real.exp (C * Real.sqrt n) :=
      prod_exp_corrections I H _ E hq.le hH hbound hE
    _ ≤ q ^ (s / 4) * Real.exp (C * Real.sqrt n) :=
      mul_le_mul_of_nonneg_right
        (prod_degreeDistance_rpow_le I e hn0 hs hq hq1 he he' hsum) (Real.exp_pos _).le
    _ ≤ n ^ (-Real.sqrt n / 20) * Real.exp (C * Real.sqrt n) :=
      mul_le_mul_of_nonneg_right (low_degree_power_saving hn hq.le hq' hs') (Real.exp_pos _).le
    _ = _ := mul_comm _ _

end Problem335

end

end OAI
