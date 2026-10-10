import OAI.NumberTheory.Ostmann.Preliminaries.Counting
import OAI.NumberTheory.Ostmann.Preliminaries.DivisorLog

namespace OAI

namespace Ostmann.QuadraticSieve
open Filter
open scoped BigOperators

def rowInflationPrimes (R : ℕ) : Finset ℕ :=
  (16*R).primesLE.filter (R < ·)

@[simp] theorem mem_rowInflationPrimes {R p : ℕ} :
    p ∈ rowInflationPrimes R ↔ p.Prime ∧ R < p ∧ p ≤ 16*R := by
  simp only [rowInflationPrimes, Finset.mem_filter, Nat.mem_primesLE]
  tauto

theorem rowInflationPrimes_odd {R p : ℕ} (hR : 2 ≤ R)
    (hp : p ∈ rowInflationPrimes R) : Odd p := by
  have h := mem_rowInflationPrimes.mp hp
  exact h.1.odd_of_ne_two (by omega)

theorem rowInflationPrimes_card_add (R : ℕ) :
    (rowInflationPrimes R).card + Nat.primeCounting R = Nat.primeCounting (16*R) := by
  have heq : (16*R).primesLE.filter (fun p => ¬ R < p) = R.primesLE := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE, not_lt]
    constructor
    · intro h
      exact ⟨h.2,h.1.2⟩
    · intro h
      exact ⟨⟨by omega,h.2⟩,h.1⟩
  have hc := Finset.card_filter_add_card_filter_not (s := (16*R).primesLE) (R < ·)
  rw [heq, Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting] at hc
  exact hc

theorem eventually_rowInflationPrimes_card_lower :
    ∀ᶠ R : ℕ in atTop,
      Real.log 2 * (R:ℝ) / Real.log R ≤ (rowInflationPrimes R).card := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcast : Tendsto (fun R : ℕ => (R:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hmul : Tendsto (fun R : ℕ => 16*R) atTop atTop :=
    tendsto_atTop_mono (fun R => by dsimp; omega) tendsto_id
  have hlower := hmul.eventually Ostmann.Preliminaries.eventually_primeCounting_lower
  have hupper := hcast.eventually (Chebyshev.eventually_primeCounting_le hlog2)
  filter_upwards [hlower,hupper,eventually_ge_atTop 16] with R hlo hup hR
  have hRr : (16:ℝ) ≤ R := by exact_mod_cast hR
  have hRp : (0:ℝ) < R := by linarith
  have hlR : 0 < Real.log (R:ℝ) := Real.log_pos (by linarith)
  have hl16R : 0 < Real.log (16*(R:ℝ)) := Real.log_pos (by nlinarith)
  have hl4 : Real.log 4 = 2*Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  have hu : (Nat.primeCounting R:ℝ) ≤ 3*Real.log 2 * (R:ℝ) / Real.log R := by
    simpa only [Nat.floor_natCast, hl4, show 2*Real.log 2+Real.log 2=3*Real.log 2 by ring] using hup
  have hlogs : Real.log (16*(R:ℝ)) ≤ 2*Real.log (R:ℝ) := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hRp)]
    linarith [Real.log_le_log (by norm_num : (0:ℝ)<16) hRr]
  have hl : 4*Real.log 2 * (R:ℝ) / Real.log R ≤ (Nat.primeCounting (16*R):ℝ) := by
    apply le_trans _ hlo
    push_cast
    apply (div_le_div_iff₀ hlR hl16R).2
    have hh := mul_le_mul_of_nonneg_left hlogs
      (show 0 ≤ 4*Real.log 2*(R:ℝ) by positivity)
    nlinarith only [hh]
  have hcard : ((rowInflationPrimes R).card:ℝ) + Nat.primeCounting R =
      Nat.primeCounting (16*R) := by exact_mod_cast rowInflationPrimes_card_add R
  calc
    _ = 4*Real.log 2*(R:ℝ)/Real.log R - 3*Real.log 2*(R:ℝ)/Real.log R := by ring
    _ ≤ (Nat.primeCounting (16*R):ℝ) - Nat.primeCounting R := sub_le_sub hl hu
    _ = _ := by linarith

theorem exists_rowInflationPrimes_card_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ R : ℕ in atTop,
      c * (R:ℝ) / Real.log R ≤ (rowInflationPrimes R).card :=
  ⟨Real.log 2, Real.log_pos (by norm_num), eventually_rowInflationPrimes_card_lower⟩

theorem card_prime_divisors_above_le (P : Finset ℕ) (R n : ℕ)
    (hR : 2 ≤ R) (hn : 0 < n) (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, R < p) :
    ((P.filter (· ∣ n)).card:ℝ) ≤ Real.log n / Real.log R := by
  have hRr : (1:ℝ) < R := by exact_mod_cast (show 1 < R by omega)
  have hlogR : 0 < Real.log (R:ℝ) := Real.log_pos hRr
  apply (le_div_iff₀ hlogR).2
  calc
    _ = ∑ _p ∈ P.filter (· ∣ n), Real.log (R:ℝ) := by simp
    _ ≤ ∑ p ∈ P.filter (· ∣ n), Real.log (p:ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact Real.log_le_log (by linarith) (by exact_mod_cast (hlarge p (Finset.mem_filter.mp hp).1).le)
    _ ≤ Real.log n := Ostmann.Preliminaries.sum_log_prime_divisors_le _ n (Nat.ne_of_gt hn)
      (fun p hp => hprime p (Finset.mem_filter.mp hp).1)
      (fun p hp => (Finset.mem_filter.mp hp).2)

theorem rowInflationPrimes_divisor_card_le (R n : ℕ) (hR : 2 ≤ R) (hn : 0 < n) :
    (((rowInflationPrimes R).filter (· ∣ n)).card:ℝ) ≤ Real.log n / Real.log R :=
  card_prime_divisors_above_le _ R n hR hn
    (fun _ hp => (mem_rowInflationPrimes.mp hp).1)
    (fun _ hp => (mem_rowInflationPrimes.mp hp).2.1)

end Ostmann.QuadraticSieve

end OAI
