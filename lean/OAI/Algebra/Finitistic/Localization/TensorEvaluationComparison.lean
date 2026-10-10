import OAI.Algebra.Finitistic.Localization.TensorEvaluationFunctor

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BalancedTensor
universe u v w z
variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
variable (M : Type w) [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M]
  [IsScalarTower k Aᵐᵒᵖ M]
variable (N : Type z) [AddCommGroup N] [Module k N] [Module A N]

def fromScalarModule : ScalarModule k A (ModuleCat.of Aᵐᵒᵖ M) →ₗ[Aᵐᵒᵖ] M where
  toFun m := m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def toScalarModule : M →ₗ[Aᵐᵒᵖ] ScalarModule k A (ModuleCat.of Aᵐᵒᵖ M) where
  toFun m := m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Compare the functor's canonical scalar restriction with an existing compatible k-action. -/
def tensorFunctorEquiv :
    (tensorFunctor k A N).obj (ModuleCat.of Aᵐᵒᵖ M) ≃ₗ[k] Tensor k A M N where
  __ := mapLeft (k := k) N (fromScalarModule (k := k) M)
  invFun := mapLeft (k := k) N (toScalarModule (k := k) M)
  left_inv z := by
    change mapLeft (k := k) N (toScalarModule (k := k) M)
      (mapLeft (k := k) N (fromScalarModule (k := k) M) z) = z
    induction z using BalancedTensor.induction_on with
    | hz => simp
    | ht m n => rfl
    | ha a b h₁ h₂ =>
      simp only [map_add]
      exact congrArg₂ (fun a b => a+b) h₁ h₂
  right_inv z := by
    change mapLeft (k := k) N (fromScalarModule (k := k) M)
      (mapLeft (k := k) N (toScalarModule (k := k) M) z) = z
    induction z using BalancedTensor.induction_on with
    | hz => simp
    | ht m n => rfl
    | ha a b h₁ h₂ =>
      simp only [map_add]
      exact congrArg₂ (fun a b => a+b) h₁ h₂

@[simp] theorem tensorFunctorEquiv_mk (m : ScalarModule k A (ModuleCat.of Aᵐᵒᵖ M)) (n : N) :
    tensorFunctorEquiv M N (mk k A (ScalarModule k A (ModuleCat.of Aᵐᵒᵖ M)) N m n) =
      mk k A M N m n := rfl
end LittleFinitistic.BalancedTensor

end

end OAI
