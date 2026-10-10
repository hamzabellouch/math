import OAI.NumberTheory.Jacobsthal.Primes.IntervalPrimesDefinition
import OAI.NumberTheory.Ostmann.Arithmetic.PrimeProgression
import OAI.NumberTheory.Ostmann.PrimeProgression.CountToHarmonicAbel

namespace OAI

open Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

open scoped BigOperators
namespace Ostmann.Arithmetic.PrimeProgression

noncomputable def primeCoefficient (M : ℕ) (a : ZMod M) (n : ℕ) : ℝ :=
  if n.Prime ∧ (n : ZMod M) = a then 1 else 0

theorem cumulativeSum_primeCoefficient (M : ℕ) (r : ℤ) {x : ℝ} (hx : 0 ≤ x) :
    cumulativeSum (primeCoefficient M (r : ZMod M)) x =
      ((Erdos970.Erdos970Dependency.SiegelWalfisz.intervalPrimes 0 x M r).card : ℝ) := by
  classical
  have hs : (Finset.Icc 0 ⌊x⌋₊).filter (fun n : ℕ => n.Prime ∧ (n : ZMod M) = (r : ZMod M)) =
      Erdos970.Erdos970Dependency.SiegelWalfisz.intervalPrimes 0 x M r := by
    ext n
    have hmod : (n : ZMod M) = (r : ZMod M) ↔ Int.ModEq (M : ℤ) (n : ℤ) r := by
      simpa only [Int.cast_natCast] using ZMod.intCast_eq_intCast_iff (n : ℤ) r M
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.zero_le, true_and,
      Erdos970.Erdos970Dependency.SiegelWalfisz.mem_intervalPrimes, zero_add]
    constructor
    · rintro ⟨hn, hp, hm⟩
      exact ⟨hp, by exact_mod_cast hp.pos, (Nat.le_floor_iff hx).mp hn, hmod.mp hm⟩
    · rintro ⟨hp, hn0, hn, hm⟩
      exact ⟨(Nat.le_floor_iff hx).mpr hn, hp, hmod.mpr hm⟩
  unfold cumulativeSum primeCoefficient
  rw [← Finset.sum_filter, hs]
  simp

noncomputable def openLogPrimeSupport (M : ℕ) (a : ZMod M) (lo hi : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊Real.exp lo⌋₊ ⌊Real.exp hi⌋₊).filter fun n => n.Prime ∧ (n : ZMod M) = a

lemma mem_openLogPrimeSupport (M : ℕ) (a : ZMod M) (lo hi : ℝ) (n : ℕ) :
    n ∈ openLogPrimeSupport M a lo hi ↔
      Real.exp lo < (n : ℝ) ∧ (n : ℝ) ≤ Real.exp hi ∧ n.Prime ∧ (n : ZMod M) = a := by
  classical
  simp only [openLogPrimeSupport, Finset.mem_filter, Finset.mem_Ioc,
    Nat.floor_lt (Real.exp_pos lo).le, Nat.le_floor_iff (Real.exp_pos hi).le, and_assoc]

theorem reciprocal_primeCoefficient_sum (M : ℕ) (a : ZMod M) (lo hi : ℝ) :
    (∑ n ∈ Finset.Ioc ⌊Real.exp lo⌋₊ ⌊Real.exp hi⌋₊, (n : ℝ)⁻¹ * primeCoefficient M a n) =
      ∑ n ∈ openLogPrimeSupport M a lo hi, (n : ℝ)⁻¹ := by
  classical
  unfold primeCoefficient openLogPrimeSupport
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_filter]

end Ostmann.Arithmetic.PrimeProgression

end OAI
