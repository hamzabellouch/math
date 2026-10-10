import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Structure.QuadraticAdjoinBasis

namespace OAI

namespace SiegelZeros

namespace WeightedTorusJets

open NumberField

attribute [local instance] canonicalCyclotomicLevelNeZero canonicalCyclotomicExtension
  canonicalCyclotomicNumberField

theorem source_biquadratic_good_prime_unramified (q p : ℕ) [NeZero q]
    (a b : CyclotomicField (8 * q) ℚ) (hp : p.Prime) (hgood : ¬ p ∣ 2 * q) :
    Algebra.IsUnramifiedIn
      (𝓞 (IntermediateField.adjoin ℚ ({a, b} : Set (CyclotomicField (8 * q) ℚ))))
      (Ideal.span {(p : ℤ)}) := by
  have : Fact p.Prime := ⟨hp⟩
  have hp8 : p ∣ 8 ↔ p ∣ 2 := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, hp.prime.dvd_pow_iff_dvd (by decide : 3 ≠ 0)]
  have hpn : ¬ p ∣ 8 * q := by simpa only [hp.dvd_mul, hp8] using hgood
  exact isUnramifiedIn_of_numberField_extension (L := CyclotomicField (8 * q) ℚ) _
    (cyclotomic_isUnramifiedIn (8 * q) (CyclotomicField (8 * q) ℚ) p hpn)

end WeightedTorusJets


end SiegelZeros

end OAI
