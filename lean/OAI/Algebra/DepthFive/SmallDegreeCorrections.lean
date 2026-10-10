import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem335

/-- A convex chord controls the small-degree correction, without differentiating
its logarithm. -/
theorem rpow_one_sub_le_chord (q z : ℝ) (hq : 0 < q)
    (hz : 0 ≤ z) (hz' : z ≤ 1 / 4) :
    q ^ (1 - z) ≤ q + 4 * z * q ^ ((3 : ℝ) / 4) := by
  have hconv : q ^ ((1 - 4 * z) * 1 + 4 * z * (3 / 4)) ≤
      (1 - 4 * z) * q ^ (1 : ℝ) + 4 * z * q ^ ((3 : ℝ) / 4) :=
    (convexOn_rpow_left hq).2
      (Set.mem_univ (1 : ℝ)) (Set.mem_univ ((3 : ℝ) / 4))
      (by linarith) (by positivity) (by ring)
  simp only [Real.rpow_one] at hconv
  have heq : (1 - 4 * z) * 1 + 4 * z * (3 / 4) = 1 - z := by ring
  rw [heq] at hconv
  have hnonneg : 0 ≤ 4 * z * q := by positivity
  nlinarith

/-- Sum version of the chord estimate. -/
theorem sum_rpow_one_sub_le_chord {ι : Type*} (I : Finset ι)
    (q : ℝ) (z : ι → ℝ) (hq : 0 < q)
    (hz : ∀ i ∈ I, 0 ≤ z i) (hz' : ∀ i ∈ I, z i ≤ 1 / 4) :
    ∑ i ∈ I, q ^ (1 - z i) ≤
      (I.card : ℝ) * q + 4 * (∑ i ∈ I, z i) * q ^ ((3 : ℝ) / 4) := by
  calc
    _ ≤ ∑ i ∈ I, (q + 4 * z i * q ^ ((3 : ℝ) / 4)) :=
      Finset.sum_le_sum (fun i hi => rpow_one_sub_le_chord q (z i) hq (hz i hi) (hz' i hi))
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
        ← Finset.sum_mul, ← Finset.mul_sum]

/-- The total low-degree correction is `O(sqrt n)`, uniformly in the number
and sizes of factors. The degree variables may be real; natural degrees are a
special case. -/
theorem sum_small_degree_corrections_le {ι : Type*} (I : Finset ι)
    (n s q : ℝ) (e : ι → ℝ)
    (hn : 0 < n) (hs : 0 ≤ s) (hs' : s ≤ Real.sqrt n)
    (hq : 0 < q) (hqone : q ≤ 1) (hqsmall : q ≤ 2 / Real.sqrt n)
    (he : ∀ i ∈ I, 1 ≤ e i)
    (helow : ∀ i ∈ I, s * e i / n ≤ 1 / 4)
    (hesum : ∑ i ∈ I, e i ≤ n) :
    ∑ i ∈ I, q ^ (1 - s * e i / n) ≤ 6 * Real.sqrt n := by
  have hpos : ∀ i ∈ I, 0 ≤ s * e i / n := by
    intro i hi
    exact div_nonneg (mul_nonneg hs (le_trans zero_le_one (he i hi))) hn.le
  have hchord := sum_rpow_one_sub_le_chord I q
    (fun i => s * e i / n) hq hpos helow
  have hcard : (I.card : ℝ) ≤ n := by
    calc
      (I.card : ℝ) = ∑ i ∈ I, (1 : ℝ) := by simp
      _ ≤ ∑ i ∈ I, e i := Finset.sum_le_sum he
      _ ≤ n := hesum
  have hsum : (∑ i ∈ I, s * e i / n) ≤ s := by
    calc
      (∑ i ∈ I, s * e i / n) = s / n * ∑ i ∈ I, e i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ s / n * n := mul_le_mul_of_nonneg_left hesum (div_nonneg hs hn.le)
      _ = s := div_mul_cancel₀ s hn.ne'
  have hsumpos : 0 ≤ ∑ i ∈ I, s * e i / n := Finset.sum_nonneg hpos
  have hqpow : q ^ ((3 : ℝ) / 4) ≤ 1 := Real.rpow_le_one hq.le hqone (by norm_num)
  have hproduct : (∑ i ∈ I, s * e i / n) * q ^ ((3 : ℝ) / 4) ≤ s := by
    calc
      _ ≤ (∑ i ∈ I, s * e i / n) * 1 :=
        mul_le_mul_of_nonneg_left hqpow hsumpos
      _ ≤ s := by simpa using hsum
  have hcardq := mul_le_mul_of_nonneg_right hcard hq.le
  have hsqrtpos := Real.sqrt_pos.mpr hn
  have hqsqrt : q * Real.sqrt n ≤ 2 := (le_div_iff₀ hsqrtpos).mp hqsmall
  have hnq : n * q ≤ 2 * Real.sqrt n := by
    calc
      n * q = Real.sqrt n * (q * Real.sqrt n) := by
        nlinarith [Real.sq_sqrt hn.le]
      _ ≤ Real.sqrt n * 2 := mul_le_mul_of_nonneg_left hqsqrt hsqrtpos.le
      _ = 2 * Real.sqrt n := mul_comm _ _
  nlinarith

end Problem335

end

end OAI
