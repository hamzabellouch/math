import OAI.NumberTheory.JointDickman.Arithmetic.DeletedPrimeFactors

namespace OAI

/-! # Exceptional large primes attached to nonzero coefficient differences -/

namespace JointDickman
open Finset

theorem prime_divisor_card_log {b : ℕ} (hb : b ≠ 0) (S : Finset ℕ)
    (hS : S ⊆ b.primeFactors) :
    (S.card : ℝ)*Real.log 2 ≤ Real.log b := by
  have hprime : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hS hp)
  have hd : (∏ p ∈ S, p) ∣ b :=
    (prod_dvd_prod_of_subset _ _ id hS).trans (Nat.prod_primeFactors_dvd b)
  have hle : (∏ p ∈ S, p : ℕ) ≤ b := Nat.le_of_dvd (Nat.pos_of_ne_zero hb) hd
  have hp0 : (0 : ℝ) < (∏ p ∈ S, p : ℕ) := by
    exact_mod_cast prod_pos (fun p hp => (hprime p hp).pos)
  exact (selectedPrime_card_log_bound S hprime).trans
    (Real.log_le_log hp0 (by exact_mod_cast hle))

/-- Only logarithmic size, nonvanishing, and the prime cutoff are needed.
This applies both to forced third-site roots and to cross-root collisions. -/
theorem large_prime_divisor_reciprocals {b : ℤ} (hb : b ≠ 0)
    (S : Finset ℕ) (hS : S ⊆ b.natAbs.primeFactors)
    {P H : ℝ} (hP : 0 < P) (hcut : ∀ p ∈ S, P ≤ (p : ℝ))
    (hsize : (b.natAbs : ℝ) ≤ Real.exp H) :
    ∑ p ∈ S, 1/(p : ℝ) ≤ H/(Real.log 2*P) := by
  have hb0 : b.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hb
  have hlog := prime_divisor_card_log hb0 S hS
  have hbpos : (0 : ℝ) < b.natAbs := by exact_mod_cast Nat.pos_of_ne_zero hb0
  have hcard : (S.card : ℝ)*Real.log 2 ≤ H :=
    hlog.trans (by simpa only [Real.log_exp] using Real.log_le_log hbpos hsize)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    _ ≤ ∑ _p ∈ S, 1/P := sum_le_sum (fun p hp => one_div_le_one_div_of_le hP (hcut p hp))
    _ = (S.card : ℝ)/P := by simp [div_eq_mul_inv]
    _ ≤ (H/Real.log 2)/P := div_le_div_of_nonneg_right ((le_div_iff₀ hlog2).mpr hcard) hP.le
    _ = _ := by ring

end JointDickman

end OAI
