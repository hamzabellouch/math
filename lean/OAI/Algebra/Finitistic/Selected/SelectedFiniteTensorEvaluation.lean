import OAI.Algebra.Finitistic.Localization.HomotopyEvaluation
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.BalancedTensor
universe u v w z
variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
variable (N : Type z) [AddCommGroup N] [Module k N] [Module A N]

instance tensorFinite (M : Type w) [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M]
    [FiniteDimensional k M] [FiniteDimensional k N] : FiniteDimensional k (Tensor k A M N) := by
  unfold Tensor
  infer_instance

theorem tensorFunctor_finite [FiniteDimensional k Aᵐᵒᵖ] [FiniteDimensional k N]
    (M : ModuleCat.{w} Aᵐᵒᵖ) [Module.Finite Aᵐᵒᵖ M] :
    FiniteDimensional k ((tensorFunctor k A N).obj M) := by
  let : Module.Finite Aᵐᵒᵖ (ScalarModule k A M) := inferInstanceAs (Module.Finite Aᵐᵒᵖ M)
  let : Module.Finite k (ScalarModule k A M) := Module.Finite.trans Aᵐᵒᵖ (ScalarModule k A M)
  exact inferInstanceAs (FiniteDimensional k (Tensor k A (ScalarModule k A M) N))

/-- The termwise evaluation preserves every actual zero term, hence bounded support. -/
theorem complex_zero (K : CochainComplex (ModuleCat.{w} Aᵐᵒᵖ) ℤ) (i : ℤ)
    (h : IsZero (K.X i)) :
    IsZero (((tensorFunctor k A N).mapHomologicalComplex (ComplexShape.up ℤ)).obj K |>.X i) :=
  (tensorFunctor k A N).map_isZero h

/-- A bounded input has a bounded output with the same interval of possible nonzero terms. -/
theorem bounded_support (K : CochainComplex (ModuleCat.{w} Aᵐᵒᵖ) ℤ) (a b : ℤ)
    (h : ∀ i, i < a ∨ b < i → IsZero (K.X i)) :
    ∀ i, i < a ∨ b < i →
      IsZero (((tensorFunctor k A N).mapHomologicalComplex (ComplexShape.up ℤ)).obj K |>.X i) :=
  fun i hi => complex_zero N K i (h i hi)
end LittleFinitistic.BalancedTensor

end

end OAI
