import OAI.Combinatorics.PolynomialVacuum.Algebra.BraidEndomorphisms
import OAI.Combinatorics.PolynomialVacuum.Algebra.Unitary

namespace OAI

namespace PolynomialVacuumAlgebra

theorem siteR_unitary (i : ℕ) (x y : ℂ) (W : SpinTensor ℕ ℂ) :
    siteR i x y (siteR i y x W)=(exchangeDenominator x y*exchangeDenominator y x) • W := by
  change pairAction i (i+1) _ (pairAction i (i+1) _ W)=_
  rw [pairAction_mul (by omega),exchange_numerator_unitarity,pairAction_smul,pairAction_one]
  rfl

theorem siteR_regular (i : ℕ) (x : ℂ) (W : SpinTensor ℕ ℂ) :
    siteR i x x W=exchangeDenominator x x • W := by
  change pairAction i (i+1) _ W=_
  rw [exchange_numerator_regular,pairAction_smul,pairAction_one]
  rfl

theorem siteR_injective (i : ℕ) (x y : ℂ)
    (hxy : exchangeDenominator x y≠0) (hyx : exchangeDenominator y x≠0) :
    Function.Injective (siteR i x y) := by
  intro A B h
  have h' := congrArg (siteR i y x) h
  rw [siteR_unitary,siteR_unitary] at h'
  funext s
  have hs := congrFun h' s
  exact mul_left_cancel₀ (mul_ne_zero hyx hxy) hs

end PolynomialVacuumAlgebra

end OAI
