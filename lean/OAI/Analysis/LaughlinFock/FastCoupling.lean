import Mathlib
import OAI.Analysis.LaughlinFock.IntegerFour

namespace OAI

/-! Fast Coupling. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder
 
def fastIntegerCoupling (c : ℤ) (z k p : ℕ) : ℤ :=
  ∑ h ∈ Finset.range (p+1), (-1)^(z-h) * (Nat.fast_choose z h : ℤ) *
    (Nat.fast_choose k (p-h) : ℤ) * c^(p-h)

theorem integerCoupling_fast (c : ℤ) (z k p : ℕ) :
    integerCoupling c z k p = fastIntegerCoupling c z k p := by
  simp only [integerCoupling, fastIntegerCoupling, Nat.choose_eq_fast_choose]

def fastIntegerCopyPolynomial (D T r p j k : ℕ) : ℤ :=
  if r ≤ j+k then
    fastIntegerCoupling 1 r (j+k-r) j * fastIntegerCoupling 1 (D-r) (T-D) p
  else 0

theorem integerCopyPolynomial_fast (D T r p j k : ℕ) :
    integerCopyPolynomial D T r p j k = fastIntegerCopyPolynomial D T r p j k := by
  simp only [integerCopyPolynomial, fastIntegerCopyPolynomial, integerCoupling_fast]
end LaughlinFock
end

end OAI
