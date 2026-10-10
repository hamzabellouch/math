import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators
open Filter Real

namespace Problem337

lemma primeCounting_nth_prime (n : ℕ) :
    (Nat.nth Nat.Prime n).primeCounting = n + 1 := by
  exact Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime n

lemma nth_prime_chebyshev_bound (n : ℕ) :
    (Nat.nth Nat.Prime n : ℝ) * Real.log 2 ≤
      ((n : ℝ) + 3) * Real.log (Nat.nth Nat.Prime n : ℝ) := by
  let p := Nat.nth Nat.Prime n
  have hp2 : 2 ≤ p := (Nat.prime_nth_prime n).two_le
  have hp2r : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by linarith)
  have hcheb := (div_le_iff₀ hlog).mp (Chebyshev.pi_ge p)
  have hpi : (p.primeCounting : ℝ) = (n : ℝ) + 1 := by
    rw [show p.primeCounting = n + 1 from primeCounting_nth_prime n]
    push_cast
    rfl
  rw [hpi] at hcheb
  have hlogplus : Real.log ((p : ℝ) + 1) ≤ 2 * Real.log (p : ℝ) := by
    calc
      Real.log ((p : ℝ) + 1) ≤ Real.log ((p : ℝ) ^ 2) :=
        Real.log_le_log (by positivity) (by nlinarith)
      _ = 2 * Real.log (p : ℝ) := by rw [Real.log_pow]; norm_num
  dsimp [p] at *
  nlinarith

lemma tendsto_nth_prime_atTop :
    Tendsto (fun n : ℕ => (Nat.nth Nat.Prime n : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono (f := fun n : ℕ => (n : ℝ))
  · intro n
    exact_mod_cast (Nat.add_two_le_nth_prime n).trans' (by omega)
  · exact tendsto_natCast_atTop_atTop

lemma eventually_log_nth_prime_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (Nat.nth Nat.Prime n : ℝ) ≤
        (1 + ε) * Real.log (n : ℝ) := by
  let r : ℝ := ε / (1 + ε)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrlt : r < 1 := by
    dsimp [r]
    apply (div_lt_one (by positivity)).2
    linarith
  have hc : 0 < Real.log 2 / 2 := by positivity
  have hsmall := (isLittleO_log_rpow_atTop hr).bound hc
  have hevent := tendsto_nth_prime_atTop.eventually hsmall
  filter_upwards [hevent, eventually_ge_atTop 3] with n hn hn3
  let p := (Nat.nth Nat.Prime n : ℝ)
  have hp : 0 < p := by
    dsimp [p]
    exact_mod_cast (Nat.prime_nth_prime n).pos
  have hp1 : 1 ≤ p := by
    dsimp [p]
    exact_mod_cast (Nat.prime_nth_prime n).one_lt.le
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn3r : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hpR : 0 < p ^ r := Real.rpow_pos_of_pos hp r
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg hp1
  have hlog2 : 0 < Real.log 2 := by positivity
  change ‖Real.log p‖ ≤ (Real.log 2 / 2) * ‖p ^ r‖ at hn
  have hbound : Real.log p ≤ (Real.log 2 / 2) * p ^ r := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlogp,
      abs_of_pos hpR] using hn
  have hcheb : p * Real.log 2 ≤ ((n : ℝ) + 3) * Real.log p :=
    nth_prime_chebyshev_bound n
  have hpre : p ≤ (n : ℝ) * p ^ r := by
    have h1 : ((n : ℝ) + 3) * Real.log p ≤ 2 * (n : ℝ) * Real.log p := by
      nlinarith
    have h2 : 2 * (n : ℝ) * Real.log p ≤
        2 * (n : ℝ) * ((Real.log 2 / 2) * p ^ r) := by
      gcongr
    nlinarith
  have hpow : p ^ (1 - r) ≤ (n : ℝ) := by
    rw [Real.rpow_sub hp, Real.rpow_one]
    exact (div_le_iff₀ hpR).2 hpre
  have hlogbound := Real.log_le_log (Real.rpow_pos_of_pos hp (1-r)) hpow
  rw [Real.log_rpow hp] at hlogbound
  have heq : (1 + ε) * (1 - r) = 1 := by
    dsimp [r]
    field_simp
    ring
  change Real.log p ≤ (1 + ε) * Real.log (n : ℝ)
  nlinarith

/-- Product of the first `n` primes, indexed from zero. -/
def primePrefixProduct (n : ℕ) : ℕ := ∏ i ∈ Finset.range n, Nat.nth Nat.Prime i

lemma primePrefixProduct_pos (n : ℕ) : 0 < primePrefixProduct n := by
  apply Finset.prod_pos
  intro i hi
  exact (Nat.prime_nth_prime i).pos

lemma primePrefixProduct_dvd_mono {m n : ℕ} (h : m ≤ n) :
    primePrefixProduct m ∣ primePrefixProduct n := by
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.range_mono h)

lemma two_pow_le_primePrefixProduct (n : ℕ) : 2 ^ n ≤ primePrefixProduct n := by
  calc
    2 ^ n = ∏ _i ∈ Finset.range n, 2 := by simp
    _ ≤ primePrefixProduct n := by
      apply Finset.prod_le_prod
      intro i hi
      exact (Nat.prime_nth_prime i).two_le

lemma log_primePrefixProduct_le (n : ℕ) :
    Real.log (primePrefixProduct n : ℝ) ≤
      (n : ℝ) * Real.log (Nat.nth Nat.Prime n : ℝ) := by
  unfold primePrefixProduct
  rw [Nat.cast_prod, Real.log_prod (by
    intro i hi
    exact_mod_cast (Nat.prime_nth_prime i).ne_zero)]
  calc
    (∑ i ∈ Finset.range n, Real.log (Nat.nth Nat.Prime i : ℝ)) ≤
        ∑ _i ∈ Finset.range n, Real.log (Nat.nth Nat.Prime n : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Real.log_le_log
      · exact_mod_cast (Nat.prime_nth_prime i).pos
      · exact_mod_cast Nat.nth_monotone Nat.infinite_setOfPred_prime
          (Finset.mem_range.mp hi).le
    _ = (n : ℝ) * Real.log (Nat.nth Nat.Prime n : ℝ) := by simp

lemma eventually_log_primePrefixProduct_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      Real.log (primePrefixProduct n : ℝ) ≤
        (1 + ε) * (n : ℝ) * Real.log (n : ℝ) := by
  filter_upwards [eventually_log_nth_prime_le hε] with n hn
  calc
    Real.log (primePrefixProduct n : ℝ) ≤
        (n : ℝ) * Real.log (Nat.nth Nat.Prime n : ℝ) := log_primePrefixProduct_le n
    _ ≤ (n : ℝ) * ((1 + ε) * Real.log (n : ℝ)) := by gcongr
    _ = _ := by ring

lemma card_divisors_primePrefixProduct (n : ℕ) :
    (primePrefixProduct n).divisors.card = 2 ^ n := by
  induction n with
  | zero => simp [primePrefixProduct]
  | succ n ih =>
    have hc : (primePrefixProduct n).Coprime (Nat.nth Nat.Prime n) := by
      apply Nat.Coprime.prod_left
      intro i hi
      apply (Nat.coprime_primes (Nat.prime_nth_prime i) (Nat.prime_nth_prime n)).2
      exact ne_of_lt (Nat.nth_strictMono Nat.infinite_setOfPred_prime (Finset.mem_range.mp hi))
    have hstep : primePrefixProduct (n + 1) = primePrefixProduct n * Nat.nth Nat.Prime n := by
      simp [primePrefixProduct, Finset.prod_range_succ]
    rw [hstep, hc.card_divisors_mul, ih, (Nat.prime_nth_prime n).divisors]
    simp [(Nat.prime_nth_prime n).ne_one.symm, pow_succ]

end Problem337

end

end OAI
