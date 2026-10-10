import OAI.NumberTheory.EgyptianFractions.PrimeProductBound

namespace OAI
open scoped BigOperators
noncomputable section
namespace Problem337

lemma card_divisors_prime_finset_product (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) : (∏ p ∈ s, p).divisors.card = 2 ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
      have hprime := hs p (by simp)
      have hcop : p.Coprime (∏ q ∈ s, q) := by
        apply Nat.Coprime.prod_right
        intro q hq
        apply (Nat.coprime_primes hprime (hs q (by simp [hq]))).2
        intro heq
        exact hp (heq ▸ hq)
      rw [Finset.prod_insert hp, hcop.card_divisors_mul, hprime.divisors,
        ih (fun q hq => hs q (by simp [hq])), Finset.card_insert_of_notMem hp]
      rw [Finset.card_pair hprime.ne_one.symm]
      simp [pow_succ, mul_comm]

/-- The product of the first `r` odd primes. -/
def oddPrimorial (r : ℕ) : ℕ := ∏ i ∈ Finset.range r, Nat.nth Nat.Prime (i + 1)

lemma oddPrimorial_pos (r : ℕ) : 0 < oddPrimorial r := by
  apply Finset.prod_pos
  intro i hi
  exact (Nat.prime_nth_prime (i+1)).pos

lemma oddPrimorial_odd (r : ℕ) : Odd (oddPrimorial r) := by
  apply Nat.Coprime.odd_of_left
  apply Nat.Coprime.prod_right
  intro i hi
  apply Odd.coprime_two_left
  apply (Nat.prime_nth_prime (i+1)).odd_iff.mpr
  have := Nat.add_two_le_nth_prime (i+1)
  omega

lemma oddPrimorial_divisors_card (r : ℕ) : (oddPrimorial r).divisors.card = 2 ^ r := by
  classical
  let f := fun i => Nat.nth Nat.Prime (i+1)
  have hf : Function.Injective f := by
    intro i j h
    have h' := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective h
    omega
  have hs : ∀ p ∈ (Finset.range r).image f, p.Prime := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact Nat.prime_nth_prime (i+1)
  have h := card_divisors_prime_finset_product ((Finset.range r).image f) hs
  rw [Finset.prod_image (fun i hi j hj hij => hf hij), Finset.card_image_iff.mpr
    (fun i hi j hj hij => hf hij), Finset.card_range] at h
  exact h

lemma oddPrimorial_gt_one (r : ℕ) (hr : 1 ≤ r) : 1 < oddPrimorial r := by
  have hcard : 2 ≤ (oddPrimorial r).divisors.card := by
    rw [oddPrimorial_divisors_card]
    exact Nat.le_self_pow (by omega) 2
  have hle := Nat.card_divisors_le_self (oddPrimorial r)
  omega


lemma primePrefixProduct_succ_eq_two_mul_oddPrimorial (r : ℕ) :
    primePrefixProduct (r+1) = 2 * oddPrimorial r := by
  rw [primePrefixProduct, Finset.prod_range_succ']
  simp [oddPrimorial, mul_comm]

lemma oddPrimorial_le_primePrefixProduct (r : ℕ) :
    oddPrimorial r ≤ primePrefixProduct (r+1) := by
  rw [primePrefixProduct_succ_eq_two_mul_oddPrimorial]
  omega

/-- A deliberately coarse size bound suffices for the representation-counting argument. -/
lemma eventually_log_log_oddPrimorial_le :
    ∀ᶠ r : ℕ in Filter.atTop,
      Real.log (Real.log (oddPrimorial r : ℝ)) ≤ 4 * Real.log (r : ℝ) := by
  have he := (Filter.tendsto_add_atTop_nat 1).eventually
    (eventually_log_primePrefixProduct_le (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [he, Filter.eventually_ge_atTop 3] with r hr hr3
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr3
  have hQr : 1 < (oddPrimorial r : ℝ) := by
    exact_mod_cast oddPrimorial_gt_one r (by omega)
  have hlogQ : 0 < Real.log (oddPrimorial r : ℝ) := Real.log_pos hQr
  have hlog : Real.log (oddPrimorial r : ℝ) ≤ (r : ℝ)^4 := by
    calc
      Real.log (oddPrimorial r : ℝ) ≤ Real.log (primePrefixProduct (r+1) : ℝ) :=
        Real.log_le_log (by linarith) (by exact_mod_cast oddPrimorial_le_primePrefixProduct r)
      _ ≤ 2 * ((r : ℝ)+1) * Real.log ((r : ℝ)+1) := by
        simpa only [Nat.cast_add, Nat.cast_one, one_add_one_eq_two] using hr
      _ ≤ 2 * ((r : ℝ)+1)^2 := by
        have hh := Real.log_le_self (show 0 ≤ (r : ℝ)+1 by positivity)
        nlinarith
      _ ≤ 8 * (r : ℝ)^2 := by nlinarith
      _ ≤ (r : ℝ)^4 := by
        have hsq : 8 ≤ (r : ℝ)^2 := by nlinarith
        have hh := mul_le_mul_of_nonneg_right hsq (sq_nonneg (r : ℝ))
        nlinarith
  have h := Real.log_le_log hlogQ hlog
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

/-- A supply of odd integers with exponentially many divisors but short double logarithm. -/
theorem eventually_odd_primorial_supply :
    ∀ᶠ r : ℕ in Filter.atTop, ∃ Q : ℕ,
      1 < Q ∧ Odd Q ∧ 2^r ≤ Q.divisors.card ∧
      Real.log (Real.log (Q : ℝ)) ≤ 4 * Real.log (r : ℝ) := by
  filter_upwards [eventually_log_log_oddPrimorial_le, Filter.eventually_ge_atTop 1] with r hr hr1
  exact ⟨oddPrimorial r, oddPrimorial_gt_one r hr1, oddPrimorial_odd r,
    (oddPrimorial_divisors_card r).ge, hr⟩

end Problem337

end

end OAI
