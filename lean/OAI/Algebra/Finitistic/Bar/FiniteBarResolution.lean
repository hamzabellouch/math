import OAI.Algebra.Finitistic.Bar.Bar
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.TensorProduct.Finite

namespace OAI
noncomputable section
open scoped TensorProduct
open CategoryTheory
namespace DerivedBar
universe u
variable (k A N : Type u) [Field k] [Ring A] [Algebra k A]
  [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
  [FiniteDimensional k A] [FiniteDimensional k N]

/-- Every absolute bar word remains finite dimensional over the base field. -/
instance term_finiteDimensional : (n : ℕ) → FiniteDimensional k (term k A N n)
  | 0 => inferInstanceAs (FiniteDimensional k N)
  | n+1 => by
    let := term_finiteDimensional n
    exact inferInstanceAs (FiniteDimensional k (A ⊗[k] term k A N n))

instance term_finite (n : ℕ) : Module.Finite A (term k A N n) :=
  Module.Finite.of_restrictScalars_finite k A (term k A N n)

/-- The actual bar projective resolution has finitely generated free terms. -/
theorem projectiveResolution_finite (n : ℕ) :
    Module.Finite A ((projectiveResolution k A N).complex.X n) :=
  term_finite k A N (n+1)
omit [FiniteDimensional k A] [FiniteDimensional k N] in
theorem projectiveResolution_free (n : ℕ) :
    Module.Free A ((projectiveResolution k A N).complex.X n) :=
  term_free k A N n
end DerivedBar

end

end OAI
