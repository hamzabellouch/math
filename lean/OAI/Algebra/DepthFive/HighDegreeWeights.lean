import OAI.Algebra.DepthFive.ProductCost
import OAI.Algebra.DepthFive.LowDegreeWeights

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- Remaining unexpanded factors cost at most one factor of five per large
occurrence, and a total exponential error for the low occurrences. -/
theorem remaining_degreeWeight_product_bound {ι : Type*} (I : Finset ι)
    (e : ι → ℕ) {n s q : ℝ} (hn : 0 < n) (hs : 0 < s)
    (hshi : s ≤ Real.sqrt n) (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (hqsqrt : q ≤ 2 / Real.sqrt n)
    (hqsmall : 5 * q ^ ((3 : ℝ) / 16) ≤ 1)
    (he : ∀ i ∈ I, 0 < e i) (hsum : (∑ i ∈ I, (e i : ℝ)) ≤ n) :
    (∏ i ∈ I, degreeWeight q (1 / 2 - s / (2 * n)) (e i)) ≤
      (5 : ℝ) ^ (4 * s) * Real.exp (24 * Real.sqrt n) := by
  classical
  have hq1 : q ≤ 1 := by linarith
  have ht : 0 < n / (4 * s) := by positivity
  have hcorr : (∑ i ∈ I with (e i : ℝ) < n / (4 * s),
      q ^ (1 - s * e i / n)) ≤ 6 * Real.sqrt n := by
    apply sum_small_degree_corrections_le
      (I.filter (fun i => (e i : ℝ) < n / (4 * s))) n s q
      (fun i => (e i : ℝ)) hn hs.le hshi hq hq1 hqsqrt
    · intro i hi
      exact_mod_cast he i (Finset.mem_filter.mp hi).1
    · intro i hi
      obtain ⟨hI, hlow⟩ := Finset.mem_filter.mp hi
      obtain ⟨_, h⟩ := low_degree_offset hn hs (he i hI) hlow
      have hid : s * e i / n = 2 * (s * e i / (2 * n)) := by ring
      rw [hid]
      linarith
    · exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => Nat.cast_nonneg (e i))).trans hsum
  have herr : (∑ i ∈ I with (e i : ℝ) < n / (4 * s),
      4 * q ^ (1 - s * e i / n)) ≤ 24 * Real.sqrt n := by
    rw [← Finset.mul_sum]
    linarith
  have hlow : ∀ i ∈ I, (e i : ℝ) < n / (4 * s) →
      degreeWeight q (1 / 2 - s / (2 * n)) (e i) ≤
        Real.exp (4 * q ^ (1 - s * e i / n)) := by
    intro i hi hlow
    have hw := low_degreeWeight_le_with_correction hn hs hq hqhalf hqsmall
      (he i hi) hlow
    have hd : 0 ≤ degreeDistance n s (e i) := nearestIntegerDistance_nonneg _
    have hp : q ^ (degreeDistance n s (e i) / 2) ≤ 1 :=
      Real.rpow_le_one hq.le hq1 (by positivity)
    exact hw.trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hp
        (Real.exp_pos (4 * q ^ (1 - s * e i / n))).le)
  have h := prod_high_low_cost_le_rpow I
    (fun i => degreeWeight q (1 / 2 - s / (2 * n)) (e i))
    (fun i => 4 * q ^ (1 - s * e i / n)) (fun i => (e i : ℝ))
    (n / (4 * s)) 5 (24 * Real.sqrt n) n ht
    (fun i _ => degreeWeight_nonneg hq.le _ _) (by norm_num)
    (fun i _ => Nat.cast_nonneg (e i)) hsum
    (fun i _ _ => degreeWeight_le_five hq hqhalf _ _) hlow herr
  have hdiv : n / (n / (4 * s)) = 4 * s := by
    field_simp
  simpa only [hdiv] using h

/-- The actual factor weights in the one-high case obey the strong power
saving required by the homogeneous depth-five circuit rank argument. -/
theorem high_degreeWeight_product_bound {ι : Type*} (I : Finset ι)
    (e : ι → ℕ) (d : ℕ) {n s q : ℝ} (hn : 1 ≤ n) (hs : 0 < s)
    (hshi : s ≤ Real.sqrt n) (hq : 0 < q) (hqhalf : q ≤ 1 / 2)
    (hqsqrt : q ≤ 2 / Real.sqrt n) (hqpow : q ≤ n ^ (-(2 : ℝ) / 5))
    (hqsmall : 5 * q ^ ((3 : ℝ) / 16) ≤ 1)
    (hlam : (3 : ℝ) / 8 ≤ 1 / 2 - s / (2 * n))
    (htone : 1 < n / (4 * s)) (hd : n / (4 * s) ≤ (d : ℝ))
    (he : ∀ i ∈ I, 0 < e i) (hsum : (∑ i ∈ I, (e i : ℝ)) ≤ n) :
    degreeWeight q (1 / 2 - s / (2 * n)) 1 ^ d *
        (∏ i ∈ I, degreeWeight q (1 / 2 - s / (2 * n)) (e i)) ≤
      (5 : ℝ) ^ (4 * s) * Real.exp (24 * Real.sqrt n) *
        n ^ (-(3 * Real.sqrt n) / 160) := by
  have hn0 : 0 < n := by linarith
  have hq1 : q ≤ 1 := by linarith
  have hdist : degreeDistance n s 1 = 1 / 2 - s / (2 * n) := by
    simpa using degreeDistance_odd hn0 hs (by decide : 0 < (1 : ℕ))
      (by simpa using htone) (by decide : Odd (1 : ℕ))
  have hlinear : degreeWeight q (1 / 2 - s / (2 * n)) 1 ≤
      q ^ ((1 / 2 - s / (2 * n)) / 2) := by
    simpa only [hdist] using low_odd_degreeWeight_le hn0 hs hq hqhalf hqsmall
      (by decide : 0 < (1 : ℕ)) (by simpa using htone) (by decide : Odd (1 : ℕ))
  have hlinpow := linear_factor_cost_power_le
    (degreeWeight q (1 / 2 - s / (2 * n)) 1) q
    (1 / 2 - s / (2 * n)) (n / (4 * s)) d
    (degreeWeight_nonneg hq.le _ _) hq hq1 (by linarith) hlinear hd
  have hprod := remaining_degreeWeight_product_bound I e hn0 hs hshi hq
    hqhalf hqsqrt hqsmall he hsum
  have ht : Real.sqrt n / 4 ≤ n / (4 * s) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * s)).mpr
    have hm := mul_le_mul_of_nonneg_left hshi (Real.sqrt_nonneg n)
    nlinarith [Real.sq_sqrt hn0.le]
  have hpower := one_high_power_saving n q (1 / 2 - s / (2 * n))
    (n / (4 * s)) hn hq.le hqpow hlam ht
  calc
    _ ≤ q ^ ((1 / 2 - s / (2 * n)) * (n / (4 * s)) / 2) *
        ((5 : ℝ) ^ (4 * s) * Real.exp (24 * Real.sqrt n)) :=
      mul_le_mul hlinpow hprod
        (Finset.prod_nonneg (fun i _ => degreeWeight_nonneg hq.le _ _))
        (Real.rpow_nonneg hq.le _)
    _ ≤ n ^ (-(3 * Real.sqrt n) / 160) *
        ((5 : ℝ) ^ (4 * s) * Real.exp (24 * Real.sqrt n)) :=
      mul_le_mul_of_nonneg_right hpower (by positivity)
    _ = _ := by ring

/-- The circuit interface only assumes `n ≥ 64`: the required slope and
threshold bounds follow from `s ≤ sqrt n`. This adapter reconciles the
canonical high-weight estimate with the circuit product interface. -/
theorem expanded_degreeWeight_product_bound {ι : Type*} (I : Finset ι) (e : ι → ℕ)
    (d : ℕ) {n s q : ℝ} (hn : 64 ≤ n) (hs : 0 < s) (hshi : s ≤ Real.sqrt n)
    (hq : 0 < q) (hqhalf : q ≤ 1 / 2) (hqsqrt : q ≤ 2 / Real.sqrt n)
    (hqpow : q ≤ n ^ (-(2 / 5 : ℝ))) (hqsmall : 5 * q ^ ((3 : ℝ) / 16) ≤ 1)
    (he : ∀ i ∈ I, 0 < e i) (hsum : ∑ i ∈ I, (e i : ℝ) ≤ n)
    (hd : n / (4 * s) ≤ (d : ℝ)) :
    (degreeWeight q (1 / 2 - s / (2 * n)) 1) ^ d *
      (∏ i ∈ I, degreeWeight q (1 / 2 - s / (2 * n)) (e i)) ≤
      (5 : ℝ) ^ (4 * s) * Real.exp (24 * Real.sqrt n) *
        n ^ (-(3 * Real.sqrt n / 160)) := by
  have hn0 : 0 < n := by linarith
  have hsq := Real.sq_sqrt hn0.le
  have hsqrt := Real.sqrt_nonneg n
  have hsqrt8 : 8 ≤ Real.sqrt n := by nlinarith
  have ht : Real.sqrt n / 4 ≤ n / (4 * s) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * s)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hshi hsqrt]
  have hdiv : s / (2 * n) ≤ 1 / 8 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * n)).mpr
    nlinarith
  simpa only [neg_div] using high_degreeWeight_product_bound I e d
    (by linarith) hs hshi hq hqhalf hqsqrt (by simpa only [neg_div] using hqpow)
    hqsmall (by linarith) (by linarith) hd he hsum

end Problem335

end

end OAI
