import OAI.NumberTheory.EgyptianFractions.RationalSupplyReduction

namespace OAI
noncomputable section
open scoped BigOperators
open Filter

namespace Problem337

/-- The odd-prime local perturbation in the ternary Goldbach singular series.
Index `n` corresponds to the integer `n + 3`; nonprimes contribute zero. -/
def threePrimeOddPerturbation (u n : ℕ) : ℝ :=
  if (n + 3).Prime then
    if n + 3 ∣ u then -(1 / ((n : ℝ) + 2) ^ 2)
    else 1 / ((n : ℝ) + 2) ^ 3
  else 0

/-- The local factor at two, with all the odd-prime factors following it. -/
def threePrimeSingularSeries (u : ℕ) : ℝ :=
  (if Odd u then 2 else 0) *
    ∏' n : ℕ, (1 + threePrimeOddPerturbation u n)

lemma threePrimeOddPerturbation_norm_le (u n : ℕ) :
    ‖threePrimeOddPerturbation u n‖ ≤ 1 / ((n : ℝ) + 2) ^ 2 := by
  have hx : 1 ≤ (n : ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hx0 : 0 < (n : ℝ) + 2 := by positivity
  unfold threePrimeOddPerturbation
  split_ifs
  · simp [Real.norm_eq_abs]
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply div_le_div_of_nonneg_left zero_le_one (by positivity)
    nlinarith [sq_nonneg ((n : ℝ) + 2)]
  · simp only [norm_zero]
    positivity

lemma threePrimeOddPerturbation_summable (u : ℕ) :
    Summable (threePrimeOddPerturbation u) := by
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 2) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (summable_nat_add_iff 2).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  exact hs.of_norm_bounded (threePrimeOddPerturbation_norm_le u)

lemma threePrimeOddFactors_multipliable (u : ℕ) :
    Multipliable (fun n : ℕ => 1 + threePrimeOddPerturbation u n) :=
  Real.multipliable_one_add_of_summable (threePrimeOddPerturbation_summable u)

/-- The telescoping product over all integers is a lower bound for the product
of the negative local factors over any subset of odd primes. -/
lemma prod_one_sub_reciprocal_square (N : ℕ) :
    (∏ n ∈ Finset.range N, (1 - 1 / ((n : ℝ) + 2) ^ 2)) =
      ((N : ℝ) + 2) / (2 * ((N : ℝ) + 1)) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.prod_range_succ, ih]
    push_cast
    have h1 : (N : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (N : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    ring

lemma one_sub_reciprocal_square_nonneg (n : ℕ) :
    0 ≤ 1 - 1 / ((n : ℝ) + 2) ^ 2 := by
  have hsq : 1 ≤ ((n : ℝ) + 2) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hdiv : 1 / ((n : ℝ) + 2) ^ 2 ≤ 1 :=
    (div_le_one (by positivity)).2 hsq
  linarith

lemma threePrimeOddFactor_lower (u n : ℕ) :
    1 - 1 / ((n : ℝ) + 2) ^ 2 ≤ 1 + threePrimeOddPerturbation u n := by
  unfold threePrimeOddPerturbation
  split_ifs <;> have h2 : 0 ≤ 1 / ((n : ℝ) + 2) ^ 2 := by positivity
  all_goals have h3 : 0 ≤ 1 / ((n : ℝ) + 2) ^ 3 := by positivity
  all_goals linarith

lemma threePrimeOddFactors_prod_lower (u N : ℕ) :
    (1 / 2 : ℝ) ≤ ∏ n ∈ Finset.range N, (1 + threePrimeOddPerturbation u n) := by
  calc
    (1 / 2 : ℝ) ≤ ((N : ℝ) + 2) / (2 * ((N : ℝ) + 1)) := by
      apply (le_div_iff₀ (by positivity)).2
      linarith
    _ = ∏ n ∈ Finset.range N, (1 - 1 / ((n : ℝ) + 2) ^ 2) :=
      (prod_one_sub_reciprocal_square N).symm
    _ ≤ _ := Finset.prod_le_prod₀
      (fun n _ => one_sub_reciprocal_square_nonneg n)
      (fun n _ => threePrimeOddFactor_lower u n)

lemma threePrimeOddFactors_tprod_lower (u : ℕ) :
    (1 / 2 : ℝ) ≤ ∏' n : ℕ, (1 + threePrimeOddPerturbation u n) := by
  exact ge_of_tendsto' (threePrimeOddFactors_multipliable u).hasProd.tendsto_prod_nat
    (threePrimeOddFactors_prod_lower u)

/-- Uniform positivity does not require a prime number theorem: the all-integer
comparison product gives the explicit lower bound one for every odd input. -/
theorem threePrimeSingularSeries_one_le {u : ℕ} (hu : Odd u) :
    1 ≤ threePrimeSingularSeries u := by
  rw [threePrimeSingularSeries, ite_eq_left hu]
  have h := threePrimeOddFactors_tprod_lower u
  linarith

/-- A uniform asymptotic error estimate for ordered prime triples suffices for
the precise quantitative number-theoretic interface used by the supply proof.
The asymptotic estimate remains a hypothesis; no Vinogradov theorem is asserted. -/
theorem quantitativeThreePrimeLowerBound_of_singular_error
    (A : ℝ) (hA : 0 < A)
    (herror : ∀ ε : ℝ, 0 < ε → ∀ᶠ u : ℕ in atTop, Odd u →
      |((supplyPrimeTriples u).card : ℝ) - A * threePrimeSingularSeries u *
        ((u : ℝ) ^ 2 / Real.log (u : ℝ) ^ 3)| ≤
      ε * ((u : ℝ) ^ 2 / Real.log (u : ℝ) ^ 3)) :
    QuantitativeThreePrimeLowerBound := by
  refine ⟨A / 2, by positivity, ?_⟩
  filter_upwards [herror (A / 2) (by positivity), eventually_ge_atTop 2] with u hu hu2
  intro hodd
  have hs := threePrimeSingularSeries_one_le hodd
  have huR : 1 < (u : ℝ) := by exact_mod_cast (show 1 < u by omega)
  have hscale : 0 ≤ (u : ℝ) ^ 2 / Real.log (u : ℝ) ^ 3 := by
    exact div_nonneg (sq_nonneg _) (pow_nonneg (Real.log_pos huR).le _)
  have hmain := mul_le_mul_of_nonneg_right hs (mul_nonneg hA.le hscale)
  have hlow := (abs_le.mp (hu hodd)).1
  nlinarith

end Problem337

end

end OAI
