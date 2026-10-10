import OAI.Algebra.Finitistic.Ordinary.OrdinaryBalancedAssociativity
import OAI.Algebra.Finitistic.Ordinary.OrdinaryTensorExactness

namespace OAI
noncomputable section
namespace LittleFinitistic
universe u
variable {k A B M M' N Z Z' : Type u} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
variable [AddCommGroup M'] [Module k M'] [Module Aᵐᵒᵖ M'] [IsScalarTower k Aᵐᵒᵖ M']
variable [AddCommGroup N] [Module k N] [Module A N] [Module Bᵐᵒᵖ N]
  [IsScalarTower k A N] [IsScalarTower k Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N]
variable [AddCommGroup Z] [Module k Z] [Module B Z] [IsScalarTower k B Z]
variable [AddCommGroup Z'] [Module k Z'] [Module B Z'] [IsScalarTower k B Z']

/-- A map of the first right module retains the middle bimodule's right B-action. -/
def RightTensor.mapFirst (f : M →ₗ[Aᵐᵒᵖ] M') : RightTensor k A B M N →ₗ[Bᵐᵒᵖ] RightTensor k A B M' N where
  __ := (BalancedTensor.mapLeft (k := k) N f).toAddHom
  map_smul' b x := by
    let F : RightTensor k A B M N →ₗ[k] RightTensor k A B M' N :=
      BalancedTensor.mapLeft (k := k) N f
    have h : F.comp (RightTensor.action k A B M N b) =
        (RightTensor.action k A B M' N b).comp F := by
      apply BalancedTensor.ext
      intro m n
      rfl
    exact congrArg (fun g => g x) h

/-- A map of the last left module retains the middle bimodule's left A-action. -/
def LeftTensor.mapLast (g : Z →ₗ[B] Z') : LeftTensor k B A N Z →ₗ[A] LeftTensor k B A N Z' where
  __ := (BalancedTensor.mapRightTo (k := k) (M := N) g).toAddHom
  map_smul' a x := by
    let F : LeftTensor k B A N Z →ₗ[k] LeftTensor k B A N Z' :=
      BalancedTensor.mapRightTo (k := k) (M := N) g
    have h : F.comp (LeftTensor.action k A B N Z a) =
        (LeftTensor.action k A B N Z' a).comp F := by
      apply BalancedTensor.ext
      intro n z
      rfl
    exact congrArg (fun g => g x) h

namespace BalancedAssociativity

omit [IsScalarTower k B Z] in
/-- Actual associativity is natural in the complex's right-module term. -/
theorem natural_first (f : M →ₗ[Aᵐᵒᵖ] M') :
    (forward k A B M' N Z).comp
      (BalancedTensor.mapLeft (k := k) Z (RightTensor.mapFirst (k := k) (B := B) (N := N) f)) =
    (BalancedTensor.mapLeft (k := k) (LeftTensor k B A N Z) f).comp (forward k A B M N Z) := by
  let F := (forward k A B M' N Z).comp
    (BalancedTensor.mapLeft (k := k) Z (RightTensor.mapFirst (k := k) (B := B) (N := N) f))
  let G := (BalancedTensor.mapLeft (k := k) (LeftTensor k B A N Z) f).comp (forward k A B M N Z)
  apply BalancedTensor.ext
  intro x z
  have h : F.comp ((BalancedTensor.mk k B (RightTensor k A B M N) Z).flip z) =
      G.comp ((BalancedTensor.mk k B (RightTensor k A B M N) Z).flip z) := by
    apply BalancedTensor.ext
    intro m n
    rfl
  exact congrArg (fun f => f x) h

omit [IsScalarTower k Aᵐᵒᵖ M] in
/-- Actual associativity is natural in the arbitrary input module. -/
theorem natural_last (g : Z →ₗ[B] Z') :
    (forward k A B M N Z').comp (BalancedTensor.mapRightTo (k := k) (M := RightTensor k A B M N) g) =
    (BalancedTensor.mapRightTo (k := k) (M := M) (LeftTensor.mapLast (k := k) (A := A) (N := N) g)).comp
      (forward k A B M N Z) := by
  let F := (forward k A B M N Z').comp
    (BalancedTensor.mapRightTo (k := k) (M := RightTensor k A B M N) g)
  let G := (BalancedTensor.mapRightTo (k := k) (M := M)
    (LeftTensor.mapLast (k := k) (A := A) (N := N) g)).comp (forward k A B M N Z)
  apply BalancedTensor.ext
  intro x z
  have h : F.comp ((BalancedTensor.mk k B (RightTensor k A B M N) Z).flip z) =
      G.comp ((BalancedTensor.mk k B (RightTensor k A B M N) Z).flip z) := by
    apply BalancedTensor.ext
    intro m n
    rfl
  exact congrArg (fun f => f x) h

end BalancedAssociativity
end LittleFinitistic

end

end OAI
