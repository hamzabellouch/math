import OAI.NumberTheory.EgyptianFractions.LargePrimeDivisors

namespace OAI
noncomputable section

open Filter

namespace Problem337

/-- At the logarithmic roughness threshold, the elementary entropy exponent
for divisors of numbers of size `exp (A log X log log X)` is sublinear in
`log X`. All estimates are uniform in the integer being factored. -/
theorem eventually_rough_entropy_le_rpow (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop,
      1 < X ∧ 1 < Real.log X ∧
      Real.log X ≤ A * Real.log X * Real.log (Real.log X) ∧
      Real.exp ((1 + Real.log
        ((A * Real.log X * Real.log (Real.log X)) / Real.log X)) *
          Real.log X / Real.log (Real.log X)) ≤ X ^ ε := by
  have hx : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have ht : Tendsto (fun X : ℝ => Real.log (Real.log X)) atTop atTop := hx.comp hx
  have hhalf : 0 < ε / 2 := by positivity
  filter_upwards [eventually_ge_atTop (2 : ℝ), hx.eventually_ge_atTop 2,
    ht.eventually_ge_atTop 1, ht.eventually_ge_atTop (1 / A),
    ht.eventually_ge_atTop (2 * (1 + |Real.log A|) / ε),
    ht.eventually (Real.isLittleO_log_id_atTop.bound hhalf)]
    with X hX hx2 ht1 htA htc hsmall
  have hxpos : 0 < Real.log X := by linarith
  have htpos : 0 < Real.log (Real.log X) := by linarith
  have hAt : 1 ≤ A * Real.log (Real.log X) := by
    have h := (div_le_iff₀ hA).mp htA
    nlinarith
  have hconst : 1 + Real.log A ≤ ε / 2 * Real.log (Real.log X) := by
    have h := (div_le_iff₀ hε).mp htc
    have hc := le_abs_self (Real.log A)
    nlinarith
  have hlogsmall : Real.log (Real.log (Real.log X)) ≤
      ε / 2 * Real.log (Real.log X) := by
    change ‖Real.log (Real.log (Real.log X))‖ ≤
      ε / 2 * ‖Real.log (Real.log X)‖ at hsmall
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos htpos] at hsmall
    exact (le_abs_self _).trans hsmall
  have hbracket : 1 + Real.log (A * Real.log (Real.log X)) ≤
      ε * Real.log (Real.log X) := by
    rw [Real.log_mul hA.ne' htpos.ne']
    linarith
  refine ⟨by linarith, by linarith, ?_, ?_⟩
  · nlinarith
  · rw [Real.rpow_def_of_pos (by linarith : 0 < X)]
    apply Real.exp_le_exp.mpr
    have hcancel : A * Real.log X * Real.log (Real.log X) / Real.log X =
        A * Real.log (Real.log X) := by
      field_simp
    rw [hcancel]
    apply (div_le_iff₀ htpos).mpr
    nlinarith [mul_le_mul_of_nonneg_right hbracket hxpos.le]

/-- Uniform subpower counting for logarithmically rough integers in the
prime-product size window. Repeated prime factors are allowed. -/
theorem eventually_truncatedDivisorCount_rough_subpower
    (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, ∀ n : ℕ, n ≠ 0 →
      Real.log (n : ℝ) ≤ A * Real.log X * Real.log (Real.log X) →
      (∀ p ∈ n.primeFactorsList, Real.log X ≤ (p : ℝ)) →
      (truncatedDivisorCount X n : ℝ) ≤ X ^ ε := by
  filter_upwards [eventually_rough_entropy_le_rpow A ε hA hε] with X hX
  intro n hn hnsize hrough
  exact (truncatedDivisorCount_large_primes_bound X (Real.log X)
    (A * Real.log X * Real.log (Real.log X)) hn hX.1 hX.2.1 hX.2.2.1
    hnsize hrough).trans hX.2.2.2

end Problem337

end

end OAI
