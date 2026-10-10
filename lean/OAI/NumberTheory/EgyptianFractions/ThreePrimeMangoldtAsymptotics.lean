import OAI.NumberTheory.EgyptianFractions.ThreePrimeMangoldt

namespace OAI
noncomputable section
open scoped BigOperators
open Filter Asymptotics

namespace Problem337

/-- Removing higher prime powers can only reduce a nonnegative convolution. -/
lemma primeTripleLogSum_le_mangoldtTripleSum (u : ℕ) :
    primeTripleLogSum u ≤ mangoldtTripleSum u := by
  rw [primeTripleLogSum_eq]
  unfold mangoldtTripleSum
  apply Finset.sum_le_sum
  intro t ht
  exact mul_le_mul
    (mul_le_mul (primeLogWeight_le_vonMangoldt t.1)
      (primeLogWeight_le_vonMangoldt t.2.1)
      (primeLogWeight_nonneg t.2.1) ArithmeticFunction.vonMangoldt_nonneg)
    (primeLogWeight_le_vonMangoldt t.2.2) (primeLogWeight_nonneg t.2.2)
    (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg)

/-- Two-sided control of the actual convolution error, without an analytic hypothesis. -/
theorem abs_mangoldtTripleSum_sub_primeTripleLogSum_le (u : ℕ) :
    |mangoldtTripleSum u - primeTripleLogSum u| ≤
      3 * (u : ℝ) * Real.log (u : ℝ) ^ 2 *
        (Chebyshev.psi u - Chebyshev.theta u) := by
  rw [abs_of_nonneg (sub_nonneg.mpr (primeTripleLogSum_le_mangoldtTripleSum u))]
  linarith [mangoldtTripleSum_le_primeTripleLogSum u]

/-- Higher prime powers do not affect the normalized quadratic main term. -/
theorem mangoldtTripleSum_sub_primeTripleLogSum_isLittleO :
    (fun u : ℕ => mangoldtTripleSum u - primeTripleLogSum u) =o[atTop]
      (fun u : ℕ => (u : ℝ) ^ 2) := by
  have hbound := mangoldt_triple_error_isLittleO.comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply IsLittleO.of_bound
  intro c hc
  filter_upwards [hbound.bound hc] with u hu
  simp only [Function.comp_apply, Real.norm_eq_abs] at hu ⊢
  exact (abs_mangoldtTripleSum_sub_primeTripleLogSum_le u).trans
    ((le_abs_self _).trans hu)

/-- The normalized difference converges to zero along all natural integers. -/
theorem tendsto_mangoldtTripleSum_sub_primeTripleLogSum_div_sq :
    Tendsto (fun u : ℕ =>
      (mangoldtTripleSum u - primeTripleLogSum u) / (u : ℝ) ^ 2)
      atTop (nhds 0) :=
  mangoldtTripleSum_sub_primeTripleLogSum_isLittleO.tendsto_div_nhds_zero

/-- Any quadratic asymptotic, including a varying singular-series coefficient,
is equivalent for the Mangoldt and prime-only convolutions. This is only an
error-transfer theorem: neither asymptotic formula is asserted. -/
theorem mangoldt_prime_quadratic_asymptotic_iff_filter
    (l : Filter ℕ) (hl : l ≤ atTop) (σ : ℕ → ℝ) :
    ((fun u : ℕ => mangoldtTripleSum u - σ u * (u : ℝ) ^ 2) =o[l]
      (fun u : ℕ => (u : ℝ) ^ 2)) ↔
    ((fun u : ℕ => primeTripleLogSum u - σ u * (u : ℝ) ^ 2) =o[l]
      (fun u : ℕ => (u : ℝ) ^ 2)) := by
  constructor
  · intro h
    exact (h.sub (mangoldtTripleSum_sub_primeTripleLogSum_isLittleO.mono hl)).congr_left
      (fun u => by ring)
  · intro h
    exact (h.add (mangoldtTripleSum_sub_primeTripleLogSum_isLittleO.mono hl)).congr_left
      (fun u => by ring)

/-- The same transfer without restricting the parameter (the filter version also
applies directly to the odd integers). -/
theorem mangoldt_prime_quadratic_asymptotic_iff (σ : ℕ → ℝ) :
    ((fun u : ℕ => mangoldtTripleSum u - σ u * (u : ℝ) ^ 2) =o[atTop]
      (fun u : ℕ => (u : ℝ) ^ 2)) ↔
    ((fun u : ℕ => primeTripleLogSum u - σ u * (u : ℝ) ^ 2) =o[atTop]
      (fun u : ℕ => (u : ℝ) ^ 2)) :=
  mangoldt_prime_quadratic_asymptotic_iff_filter atTop le_rfl σ

end Problem337

end

end OAI
