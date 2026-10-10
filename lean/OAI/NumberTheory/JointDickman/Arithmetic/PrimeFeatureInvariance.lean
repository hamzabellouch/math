import OAI.NumberTheory.JointDickman.Arithmetic.PrimeFeatureShortError
import OAI.NumberTheory.JointDickman.Arithmetic.ScaledRoughCoefficients

namespace OAI

/-! # Fixed multipliers leave the auxiliary-prime features unchanged -/
namespace JointDickman
open Finset Filter Classical

theorem primeSiteWeight_mul_fixed (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (F : (Q → Bool) → ℝ) {d : ℕ} (hd : d ≠ 0)
    (hno : ∀ p ∈ Q, ¬p ∣ d) (k : ℕ) :
    primeSiteWeight Q F (d*k) = primeSiteWeight Q F k := by
  by_cases hk : k = 0
  · simp [hk]
  rw [primeSiteWeight_apply Q F (mul_ne_zero hd hk),primeSiteWeight_apply Q F hk]
  congr 1
  funext p
  simp only [(hQ p p.property).dvd_mul,hno p p.property,false_or]

theorem auxiliaryPrimes_eventually_no_factor {d : ℕ} (hd : d ≠ 0) :
    ∀ᶠ B in atTop, ∀ p ∈ auxiliaryPrimes B, ¬p ∣ d := by
  filter_upwards [auxiliaryCutoff_tendsto.eventually_ge_atTop d] with B hB
  intro p hp hpd
  have hlarge : (auxiliaryCutoff B : ℝ) < p := (mem_filter.mp hp).2
  have hle : p ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero hd) hpd
  have hh : (p : ℝ) ≤ auxiliaryCutoff B := by exact_mod_cast hle.trans hB
  exact (not_lt_of_ge hh) hlarge

theorem auxiliaryPrimeFeature_eventually_mul_fixed {d : ℕ} (hd : d ≠ 0)
    (F : ∀ B, (auxiliaryPrimes B → Bool) → ℝ) :
    ∀ᶠ B in atTop, ∀ k, primeSiteWeight (auxiliaryPrimes B) (F B) (d*k) =
      primeSiteWeight (auxiliaryPrimes B) (F B) k := by
  filter_upwards [auxiliaryPrimes_eventually_no_factor hd] with B hB
  exact primeSiteWeight_mul_fixed _ (auxiliaryPrimes_prime B) _ hd hB

end JointDickman

end OAI
