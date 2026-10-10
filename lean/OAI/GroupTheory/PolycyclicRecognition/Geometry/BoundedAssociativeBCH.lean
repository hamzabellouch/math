import OAI.GroupTheory.PolycyclicRecognition.Geometry.FiniteAssociativeBCH
import OAI.GroupTheory.PolycyclicRecognition.Geometry.UniversalBCHCoefficientBound
import Mathlib.Algebra.Module.Rat

namespace OAI

/-! # Real coefficients and the bounded associative BCH identity -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators
attribute [local instance 100] LieRing.ofAssociativeRing

def universalDynkinCoefficients (c n : ℕ) : DynkinCoefficients c n :=
  fun d w => (((d.val + 1 : ℚ)⁻¹ *
    (universalLogarithmCoefficient c n (d.val + 1)).coeff (wordOfFn w) : ℚ) : ℝ)

theorem universalDynkinCoefficients_bound (c n : ℕ) (d : Fin c)
    (w : Fin (d.val + 1) → Fin n) :
    |universalDynkinCoefficients c n d w| ≤ (2 : ℝ) ^ c := by
  unfold universalDynkinCoefficients
  exact_mod_cast universalBCHCoefficient_bound c n d w

variable {A : Type*} [Ring A] [Algebra ℝ A] [Algebra ℚ A]
variable {c n : ℕ} (X : Fin n → A)

theorem universalDynkinPolynomial_eq :
    finiteDynkinPolynomial (universalDynkinCoefficients c n) X =
      finiteUniversalLiePolynomial (c := c) X := by
  unfold finiteDynkinPolynomial finiteUniversalLiePolynomial universalDynkinCoefficients
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro w _
  exact Rat.cast_smul_eq_qsmul ℝ _ _

theorem bounded_associative_bch
    (hX : ∀ w : FreeMonoid (Fin n), c < w.length → FreeMonoid.lift X w = 0) :
    (List.ofFn (fun i => IsNilpotent.exp (X i))).prod =
      IsNilpotent.exp (finiteDynkinPolynomial (universalDynkinCoefficients c n) X) := by
  rw [universalDynkinPolynomial_eq]
  exact finite_associative_bch X hX

end PolycyclicRecognition

end

end OAI
