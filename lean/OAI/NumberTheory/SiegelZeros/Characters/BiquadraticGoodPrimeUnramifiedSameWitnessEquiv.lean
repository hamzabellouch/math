import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Characters.BiquadraticGoodPrimeUnramified

namespace OAI

namespace SiegelZeros

open scoped NumberField
namespace WeightedTorusJets

open NumberField

attribute [local instance] canonicalCyclotomicLevelNeZero canonicalCyclotomicExtension
  canonicalCyclotomicNumberField

theorem source_biquadratic_good_prime_unramified_same_witness_equiv
    (q p : ℕ) [NeZero q] (a b : CyclotomicField (8 * q) ℚ)
    {K : Type*} [Field K] [NumberField K]
    (e : IntermediateField.adjoin ℚ ({a, b} : Set (CyclotomicField (8 * q) ℚ)) ≃ₐ[ℚ] K)
    (hp : p.Prime) (hgood : ¬ p ∣ 2 * q) :
    Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(p : ℤ)}) := by
  let := e.symm.toRingHom.toAlgebra
  exact isUnramifiedIn_of_numberField_extension _
    (source_biquadratic_good_prime_unramified q p a b hp hgood)

end WeightedTorusJets


end SiegelZeros

end OAI
