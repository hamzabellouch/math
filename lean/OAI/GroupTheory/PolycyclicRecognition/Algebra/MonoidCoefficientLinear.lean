import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Algebra.Algebra.Rat

namespace OAI

/-! # Coefficientwise rational linear maps on monoid algebras -/

noncomputable section
namespace PolycyclicRecognition

variable {R S M : Type*} [Semiring R] [Semiring S] [Module ℚ R] [Module ℚ S]

def monoidCoefficientLinear (f : R →ₗ[ℚ] S) : MonoidAlgebra R M →ₗ[ℚ] MonoidAlgebra S M :=
  (MonoidAlgebra.coeffLinearEquiv ℚ).symm.toLinearMap.comp
    ((Finsupp.mapRange.linearMap f).comp (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap)

@[simp] theorem monoidCoefficientLinear_coeff (f : R →ₗ[ℚ] S) (p : MonoidAlgebra R M) (m : M) :
    (monoidCoefficientLinear f p).coeff m = f (p.coeff m) := rfl

@[simp] theorem monoidCoefficientLinear_single (f : R →ₗ[ℚ] S) (m : M) (r : R) :
    monoidCoefficientLinear f (MonoidAlgebra.single m r) = MonoidAlgebra.single m (f r) := by
  classical
  ext m'
  by_cases h : m = m'
  · subst m'; simp
  · simp [MonoidAlgebra.coeff_single, h]

variable [Monoid M]

theorem monoidCoefficientLinear_single_mul (f : R →ₗ[ℚ] S) (m : M) (p : MonoidAlgebra R M) :
    monoidCoefficientLinear f (MonoidAlgebra.single m 1 * p) =
      MonoidAlgebra.single m 1 * monoidCoefficientLinear f p := by
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [mul_add, map_add, hp, hq]
  | single n r => simp

theorem monoidCoefficientLinear_mapDomain {N : Type*} (f : R →ₗ[ℚ] S) (g : M → N)
    (p : MonoidAlgebra R M) :
    monoidCoefficientLinear f (MonoidAlgebra.mapDomain g p) =
      MonoidAlgebra.mapDomain g (monoidCoefficientLinear f p) := by
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [MonoidAlgebra.mapDomain_add, map_add, hp, hq]
  | single m r => simp

end PolycyclicRecognition

end

end OAI
