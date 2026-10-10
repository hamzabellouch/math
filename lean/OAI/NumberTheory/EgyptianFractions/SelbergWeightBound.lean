import OAI.NumberTheory.EgyptianFractions.SelbergOptimal

namespace OAI
noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius
open Finset

namespace Problem337.SelbergOptimal

/-- Summation over the divisors of a coprime product has no multiplicities. -/
theorem sum_coprime_divisors {a b : ℕ} (hab : a.Coprime b) (f : ℕ → ℝ) :
    (∑ d ∈ (a * b).divisors, f d) =
      ∑ e ∈ a.divisors, ∑ t ∈ b.divisors, f (e * t) := by
  rw [hab.divisors_mul]
  simp only [sum_map]
  exact (sum_attach (a.divisors ×ˢ b.divisors)
    (fun p : ℕ × ℕ => f (p.1 * p.2))).trans (sum_product _ _ _)

/-- The complementary divisor of a squarefree integer is coprime to it. -/
theorem coprime_complement (s : BoundingSieve) {d : ℕ} (hd : d ∣ s.prodPrimes) :
    d.Coprime (s.prodPrimes / d) := by
  apply Nat.coprime_of_squarefree_mul
  simpa only [Nat.mul_div_cancel' hd] using s.prodPrimes_squarefree

/-- Split the finite Selberg normalizer at a divisor of the sieving product. -/
theorem normalizer_decompose (s : BoundingSieve) (z : ℕ) {d : ℕ}
    (hd : d ∣ s.prodPrimes) :
    normalizer s z =
      ∑ e ∈ d.divisors, ∑ t ∈ (s.prodPrimes / d).divisors,
        if e * t ≤ z then s.selbergTerms e * s.selbergTerms t else 0 := by
  have hcop := coprime_complement s hd
  unfold normalizer
  conv_lhs => rw [← Nat.mul_div_cancel' hd]
  rw [sum_coprime_divisors hcop]
  apply sum_congr rfl
  intro e he
  apply sum_congr rfl
  intro t ht
  rw [s.selbergTerms_isMultiplicative.map_mul_of_coprime
    (hcop.coprime_dvd_left (Nat.dvd_of_mem_divisors he) |>.coprime_dvd_right
      (Nat.dvd_of_mem_divisors ht))]

theorem sum_selbergTerms_divisors (s : BoundingSieve) {d : ℕ}
    (hd : d ∣ s.prodPrimes) :
    (∑ e ∈ d.divisors, s.selbergTerms e) = s.selbergTerms d / s.nu d := by
  have h := s.sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv hd
  rw [← sum_filter, Nat.divisors_filter_dvd_of_dvd s.prodPrimes_ne_zero hd] at h
  simpa only [div_eq_mul_inv] using h

/-- The positive numerator of an optimal Selberg weight is a subsum of the
normalizer, after splitting into complementary divisor coordinates. -/
theorem truncated_complement_sum_le_normalizer (s : BoundingSieve) (z : ℕ)
    {d : ℕ} (hd : d ∣ s.prodPrimes) :
    (s.selbergTerms d / s.nu d) *
        (∑ t ∈ (s.prodPrimes / d).divisors,
          if d * t ≤ z then s.selbergTerms t else 0) ≤ normalizer s z := by
  rw [← sum_selbergTerms_divisors s hd, sum_mul,
    normalizer_decompose s z hd]
  apply sum_le_sum
  intro e he
  rw [mul_sum]
  apply sum_le_sum
  intro t ht
  have heP := (Nat.dvd_of_mem_divisors he).trans hd
  have htP := (Nat.dvd_of_mem_divisors ht).trans (Nat.div_dvd_of_dvd hd)
  have he0 := (s.selbergTerms_pos heP).le
  have ht0 := (s.selbergTerms_pos htP).le
  by_cases hdt : d * t ≤ z
  · have het : e * t ≤ z :=
      (Nat.mul_le_mul_right t (Nat.le_of_dvd
        (Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hd))
        (Nat.dvd_of_mem_divisors he))).trans hdt
    simp only [ite_eq_left hdt, ite_eq_left het, le_refl]
  · simp only [ite_eq_right hdt, mul_zero]
    split_ifs <;> positivity

/-- The same bound in the quotient-cutoff form used in the explicit weights. -/
theorem truncated_div_sum_le_normalizer (s : BoundingSieve) (z : ℕ)
    {d : ℕ} (hd : d ∣ s.prodPrimes) :
    (s.selbergTerms d / s.nu d) *
        (∑ t ∈ (s.prodPrimes / d).divisors,
          if t ≤ z / d then s.selbergTerms t else 0) ≤ normalizer s z := by
  have hd0 : 0 < d :=
    Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hd)
  simpa only [Nat.le_div_iff_mul_le hd0, Nat.mul_comm] using
    truncated_complement_sum_le_normalizer s z hd

/-- The normalized explicit optimal-weight expression has absolute value at
most one. This bound is independent of the local sieve dimension. -/
theorem abs_normalized_complement_le_one (s : BoundingSieve) {z : ℕ}
    (hz : 1 ≤ z) {d : ℕ} (hd : d ∣ s.prodPrimes) :
    |(μ d : ℝ) * (s.selbergTerms d / s.nu d) /
        normalizer s z *
        (∑ t ∈ (s.prodPrimes / d).divisors,
          if t ≤ z / d then s.selbergTerms t else 0)| ≤ 1 := by
  have hG := normalizer_pos s hz
  have hnu := s.nu_pos_of_dvd_prodPrimes hd
  have hg := s.selbergTerms_pos hd
  have hsum : 0 ≤ ∑ t ∈ (s.prodPrimes / d).divisors,
      if t ≤ z / d then s.selbergTerms t else 0 := by
    apply sum_nonneg
    intro t ht
    split_ifs
    · exact (s.selbergTerms_pos ((Nat.dvd_of_mem_divisors ht).trans
        (Nat.div_dvd_of_dvd hd))).le
    · exact le_rfl
  have hmu : |(μ d : ℝ)| = 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree
      (s.squarefree_of_dvd_prodPrimes hd)
  rw [abs_mul, abs_div, abs_mul, hmu, one_mul,
    abs_of_pos (div_pos hg hnu), abs_of_pos hG, abs_of_nonneg hsum]
  rw [div_mul_eq_mul_div, div_le_one hG]
  exact truncated_div_sum_le_normalizer s z hd

end Problem337.SelbergOptimal

end

end OAI
