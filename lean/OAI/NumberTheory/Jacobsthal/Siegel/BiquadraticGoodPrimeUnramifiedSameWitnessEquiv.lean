import Mathlib
import PrimeNumberTheoremAnd.Erdos970.HadamardSupport
import OAI.NumberTheory.Jacobsthal.Siegel.BiquadraticGoodPrimeUnramified

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
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

end

end Erdos970

end OAI
