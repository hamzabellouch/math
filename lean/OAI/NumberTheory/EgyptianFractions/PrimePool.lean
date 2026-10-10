import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators
open Filter Asymptotics

namespace Problem337

/-- A coarse elementary lower estimate for the prime counting function. -/
theorem eventually_prime_count_lower :
    ∀ᶠ x : ℝ in atTop, x / (4 * Real.log x) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  have hsmall := ((isLittleO_const_id_atTop (2 * Real.log 2)).add
    Real.isLittleO_log_id_atTop).bound (c := 1 / 4) (by norm_num)
  filter_upwards [hsmall, eventually_ge_atTop (2 : ℝ)] with x hs hx
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have herror : 2 * Real.log 2 + Real.log x ≤ x / 4 := by
    have hh := (le_abs_self (2 * Real.log 2 + Real.log x)).trans (by simpa only [Real.norm_eq_abs] using hs)
    simpa [Real.norm_eq_abs, abs_of_nonneg hxpos.le, div_eq_mul_inv, mul_comm] using hh
  have hshift : Real.log (x + 2) ≤ Real.log 2 + Real.log x := by
    calc
      Real.log (x + 2) ≤ Real.log (2 * x) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 2 + Real.log x := Real.log_mul (by norm_num) hxpos.ne'
  have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  calc
    x / (4 * Real.log x) = (x / 4) / Real.log x := by ring
    _ ≤ ((x - 1) * Real.log 2 - Real.log (x + 2)) / Real.log x := by
      apply div_le_div_of_nonneg_right _ hlogpos.le
      nlinarith
    _ ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := Chebyshev.pi_ge' (by linarith)

/-- A coarse elementary upper estimate for the prime counting function. -/
theorem eventually_prime_count_upper :
    ∀ᶠ x : ℝ in atTop, (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ 5 * x / Real.log x := by
  have hsmall := (isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).bound
    (c := 1) (by norm_num)
  filter_upwards [hsmall, eventually_ge_atTop (2 : ℝ)] with x hs hx
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogsmall : Real.log x ≤ Real.sqrt x := by
    have hh := (le_abs_self (Real.log x)).trans (by simpa only [Real.norm_eq_abs] using hs)
    simpa [Real.norm_eq_abs, Real.sqrt_eq_rpow, abs_of_nonneg (Real.rpow_nonneg hxpos.le _)] using hh
  have hsqrt : Real.sqrt x ≤ x / Real.log x := by
    apply (le_div_iff₀ hlogpos).mpr
    calc
      Real.sqrt x * Real.log x ≤ Real.sqrt x * Real.sqrt x :=
        mul_le_mul_of_nonneg_left hlogsmall (Real.sqrt_nonneg x)
      _ = x := Real.mul_self_sqrt hxpos.le
  have hlogfour : Real.log 4 ≤ 2 := by
    have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have heq : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith
  calc
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ Real.log 4 * x / Real.log (Real.sqrt x) + Real.sqrt x :=
      Chebyshev.pi_le_log4_mul_div (by linarith)
    _ = 2 * Real.log 4 * x / Real.log x + Real.sqrt x := by
      rw [Real.log_sqrt hxpos.le]; ring
    _ ≤ 4 * x / Real.log x + x / Real.log x := by
      apply add_le_add _ hsqrt
      apply div_le_div_of_nonneg_right _ hlogpos.le
      nlinarith
    _ = 5 * x / Real.log x := by ring

/-- A prime pool in a fixed-width multiplicative interval. -/
def widePrimePool (x : ℝ) : Finset ℕ :=
  Nat.primesLE ⌊64 * x⌋₊ \ Nat.primesLE ⌊x⌋₊

theorem eventually_wide_prime_pool_large :
    ∀ᶠ x : ℝ in atTop,
      x / Real.log x ≤ ((widePrimePool x).card : ℝ) := by
  have hscale : Tendsto (fun x : ℝ => 64 * x) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) tendsto_id
  filter_upwards [hscale.eventually eventually_prime_count_lower,
    eventually_prime_count_upper, eventually_ge_atTop (64 : ℝ)] with x hl hu hx
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hloglargepos : 0 < Real.log (64 * x) := Real.log_pos (by nlinarith)
  have hloglarge : Real.log (64 * x) ≤ 2 * Real.log x := by
    rw [Real.log_mul (by norm_num) hxpos.ne']
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 64) hx
    linarith
  have hlow : 8 * x / Real.log x ≤ (Nat.primeCounting ⌊64 * x⌋₊ : ℝ) := by
    apply le_trans _ hl
    apply (div_le_div_iff₀ hlogpos (by positivity : 0 < 4 * Real.log (64 * x))).mpr
    nlinarith [mul_le_mul_of_nonneg_left hloglarge (show 0 ≤ 32 * x by positivity)]
  have hsub : Nat.primesLE ⌊x⌋₊ ⊆ Nat.primesLE ⌊64 * x⌋₊ :=
    Nat.primesLE_mono (Nat.floor_mono (by nlinarith))
  have hcards := Finset.card_le_card hsub
  rw [widePrimePool, Finset.card_sdiff_of_subset hsub, Nat.cast_sub hcards,
    Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]
  have hratio : 0 ≤ x / Real.log x := by positivity
  simp only [mul_div_assoc] at hu hlow
  linarith

/-- The residue construction needs polynomially many primes at scale `S^100`.
Chebyshev's elementary estimates suffice if the fixed interval width is 64. -/
theorem eventually_residue_prime_pool_large :
    ∀ᶠ S : ℝ in atTop,
      S ^ 99 ≤ ((widePrimePool (S ^ 100)).card : ℝ) := by
  have hp : Tendsto (fun S : ℝ => S ^ 100) atTop atTop :=
    tendsto_pow_atTop (by norm_num)
  have hsmall := Real.isLittleO_log_id_atTop.bound (c := 1 / 100) (by norm_num)
  filter_upwards [hp.eventually eventually_wide_prime_pool_large,
    hsmall, eventually_ge_atTop (2 : ℝ)] with S hpool hs hS
  have hSpos : 0 < S := by linarith
  have hlogpos : 0 < Real.log S := Real.log_pos (by linarith)
  have hlogsmall : 100 * Real.log S ≤ S := by
    have hh := (le_abs_self (Real.log S)).trans (by simpa only [Real.norm_eq_abs] using hs)
    simp only [id_eq, abs_of_nonneg hSpos.le] at hh
    linarith
  apply le_trans _ hpool
  rw [Real.log_pow]
  norm_num
  apply (le_div_iff₀ (by positivity : 0 < 100 * Real.log S)).mpr
  calc
    S ^ 99 * (100 * Real.log S) ≤ S ^ 99 * S :=
      mul_le_mul_of_nonneg_left hlogsmall (by positivity)
    _ = S ^ 100 := by ring

/-- Membership records the exact real endpoints, without rounding ambiguity. -/
theorem mem_widePrimePool_iff {x : ℝ} (hx : 0 ≤ x) {p : ℕ} :
    p ∈ widePrimePool x ↔ Nat.Prime p ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 64 * x := by
  simp only [widePrimePool, Finset.mem_sdiff, Nat.mem_primesLE,
    Nat.le_floor_iff (mul_nonneg (by norm_num : (0 : ℝ) ≤ 64) hx), Nat.le_floor_iff hx]
  constructor
  · rintro ⟨⟨hupper, hprime⟩, hnot⟩
    refine ⟨hprime, ?_, hupper⟩
    exact lt_of_not_ge (fun h => hnot ⟨h, hprime⟩)
  · rintro ⟨hprime, hlower, hupper⟩
    exact ⟨⟨hupper, hprime⟩, fun h => (not_le_of_gt hlower) h.1⟩

/-- Full elementary prime-pool interface for the residue construction. -/
theorem eventually_residue_prime_pool_spec :
    ∀ᶠ S : ℝ in atTop,
      S ^ 99 ≤ ((widePrimePool (S ^ 100)).card : ℝ) ∧
      ∀ p ∈ widePrimePool (S ^ 100),
        Nat.Prime p ∧ S ^ 100 < (p : ℝ) ∧ (p : ℝ) ≤ S ^ 101 := by
  filter_upwards [eventually_residue_prime_pool_large,
    eventually_ge_atTop (64 : ℝ)] with S hcard hS
  refine ⟨hcard, ?_⟩
  intro p hp
  obtain ⟨hprime, hlower, hupper⟩ := (mem_widePrimePool_iff (by positivity)).mp hp
  refine ⟨hprime, hlower, hupper.trans ?_⟩
  calc
    64 * S ^ 100 ≤ S * S ^ 100 := mul_le_mul_of_nonneg_right hS (by positivity)
    _ = S ^ 101 := by ring

end Problem337

end

end OAI
