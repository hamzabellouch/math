import OAI.Algebra.Finitistic.Ordinary.OrdinaryAssociativeTensorModules
import Mathlib.Tactic.Abel

namespace OAI
noncomputable section
namespace LittleFinitistic.BalancedAssociativity
open BalancedTensor
universe u
variable (k A B M N Z : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M]
variable [AddCommGroup N] [Module k N] [Module A N] [Module Bᵐᵒᵖ N]
  [IsScalarTower k A N] [IsScalarTower k Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N]
variable [AddCommGroup Z] [Module k Z] [Module B Z]

abbrev Left := Tensor k B (RightTensor k A B M N) Z
abbrev Right := Tensor k A M (LeftTensor k B A N Z)

/-- Reassociate a fixed last input through the actual A-balanced quotient. -/
def forwardAt (z : Z) : RightTensor k A B M N →ₗ[k] Right k A B M N Z :=
  lift ((mk k A M (LeftTensor k B A N Z)).compl₁₂ LinearMap.id ((LeftTensor.mk k A B N Z).flip z)) (by
    intro a m n
    change mk k A M (LeftTensor k B A N Z) (MulOpposite.op a • m) (LeftTensor.mk k A B N Z n z) =
      mk k A M (LeftTensor k B A N Z) m (LeftTensor.mk k A B N Z (a • n) z)
    rw [balance,LeftTensor.smul_mk])

@[simp] theorem forwardAt_mk (m : M) (n : N) (z : Z) :
    forwardAt k A B M N Z z (RightTensor.mk k A B M N m n) =
      mk k A M (LeftTensor k B A N Z) m (LeftTensor.mk k A B N Z n z) := rfl

def forwardBilinear : RightTensor k A B M N →ₗ[k] Z →ₗ[k] Right k A B M N Z where
  toFun x :=
    { toFun := fun z => forwardAt k A B M N Z z x
      map_add' := fun z z' => by
        have h : forwardAt k A B M N Z (z+z') =
            forwardAt k A B M N Z z + forwardAt k A B M N Z z' := by
          apply BalancedTensor.ext
          intro m n
          change mk k A M (LeftTensor k B A N Z) m (LeftTensor.mk k A B N Z n (z+z')) =
            mk k A M (LeftTensor k B A N Z) m (LeftTensor.mk k A B N Z n z) +
            mk k A M (LeftTensor k B A N Z) m (LeftTensor.mk k A B N Z n z')
          simp only [map_add]
        exact congrArg (fun f => f x) h
      map_smul' := fun r z => by
        have h : forwardAt k A B M N Z (r • z) = r • forwardAt k A B M N Z z := by
          apply BalancedTensor.ext
          intro m n
          change mk k A M (LeftTensor k B A N Z) m (LeftTensor.mk k A B N Z n (r • z)) =
            r • mk k A M (LeftTensor k B A N Z) m (LeftTensor.mk k A B N Z n z)
          simp only [map_smul]
        exact congrArg (fun f => f x) h }
  map_add' x y := by ext z; exact (forwardAt k A B M N Z z).map_add x y
  map_smul' r x := by ext z; exact (forwardAt k A B M N Z z).map_smul r x

/-- The actual forward associativity map of balanced tensors. -/
def forward : Left k A B M N Z →ₗ[k] Right k A B M N Z :=
  lift (forwardBilinear k A B M N Z) (by
    intro b x z
    have h : (forwardAt k A B M N Z z).comp (RightTensor.action k A B M N (MulOpposite.op b)) =
        forwardAt k A B M N Z (b • z) := by
      apply BalancedTensor.ext
      intro m n
      change forwardAt k A B M N Z z (MulOpposite.op b • RightTensor.mk k A B M N m n) =
        forwardAt k A B M N Z (b • z) (RightTensor.mk k A B M N m n)
      rw [RightTensor.smul_mk,forwardAt_mk,forwardAt_mk]
      exact congrArg (mk k A M (LeftTensor k B A N Z) m) (balance b n z)
    exact congrArg (fun f => f x) h)


@[simp] theorem forward_mk (m : M) (n : N) (z : Z) :
    forward k A B M N Z (mk k B (RightTensor k A B M N) Z (RightTensor.mk k A B M N m n) z) =
      mk k A M (LeftTensor k B A N Z) m (LeftTensor.mk k A B N Z n z) := rfl

/-- Reassociate a fixed first input through the actual B-balanced quotient. -/
def inverseAt (m : M) : LeftTensor k B A N Z →ₗ[k] Left k A B M N Z :=
  lift ((mk k B (RightTensor k A B M N) Z).compl₁₂ (RightTensor.mk k A B M N m) LinearMap.id) (by
    intro b n z
    change mk k B (RightTensor k A B M N) Z (RightTensor.mk k A B M N m (MulOpposite.op b • n)) z =
      mk k B (RightTensor k A B M N) Z (RightTensor.mk k A B M N m n) (b • z)
    rw [← RightTensor.smul_mk,balance])

@[simp] theorem inverseAt_mk (m : M) (n : N) (z : Z) :
    inverseAt k A B M N Z m (LeftTensor.mk k A B N Z n z) =
      mk k B (RightTensor k A B M N) Z (RightTensor.mk k A B M N m n) z := rfl

def inverseBilinear : M →ₗ[k] LeftTensor k B A N Z →ₗ[k] Left k A B M N Z where
  toFun := inverseAt k A B M N Z
  map_add' m m' := by
    apply BalancedTensor.ext
    intro n z
    change mk k B (RightTensor k A B M N) Z (RightTensor.mk k A B M N (m+m') n) z =
      mk k B (RightTensor k A B M N) Z (RightTensor.mk k A B M N m n) z +
      mk k B (RightTensor k A B M N) Z (RightTensor.mk k A B M N m' n) z
    simp only [map_add,LinearMap.add_apply]
  map_smul' r m := by
    apply BalancedTensor.ext
    intro n z
    change mk k B (RightTensor k A B M N) Z (RightTensor.mk k A B M N (r • m) n) z =
      r • mk k B (RightTensor k A B M N) Z (RightTensor.mk k A B M N m n) z
    simp only [map_smul,LinearMap.smul_apply]

/-- The actual inverse associativity map of balanced tensors. -/
def inverse : Right k A B M N Z →ₗ[k] Left k A B M N Z :=
  lift (inverseBilinear k A B M N Z) (by
    intro a m x
    have h : inverseAt k A B M N Z (MulOpposite.op a • m) =
        (inverseAt k A B M N Z m).comp (LeftTensor.action k A B N Z a) := by
      apply BalancedTensor.ext
      intro n z
      change inverseAt k A B M N Z (MulOpposite.op a • m) (LeftTensor.mk k A B N Z n z) =
        inverseAt k A B M N Z m (a • LeftTensor.mk k A B N Z n z)
      rw [LeftTensor.smul_mk,inverseAt_mk,inverseAt_mk]
      exact congrArg (fun y => mk k B (RightTensor k A B M N) Z y z) (balance a m n)
    exact congrArg (fun f => f x) h)


@[simp] theorem inverse_mk (m : M) (n : N) (z : Z) :
    inverse k A B M N Z (mk k A M (LeftTensor k B A N Z) m (LeftTensor.mk k A B N Z n z)) =
      mk k B (RightTensor k A B M N) Z (RightTensor.mk k A B M N m n) z := rfl

/-- Associativity of the actual noncommutative balanced tensor, with no flatness hypotheses. -/
def equivalence : Left k A B M N Z ≃ₗ[k] Right k A B M N Z where
  __ := forward k A B M N Z
  invFun := inverse k A B M N Z
  left_inv x := by
    let F := (inverse k A B M N Z).comp (forward k A B M N Z)
    have h : F = LinearMap.id := by
      apply BalancedTensor.ext
      intro y z
      have hz : F.comp ((mk k B (RightTensor k A B M N) Z).flip z) =
          (mk k B (RightTensor k A B M N) Z).flip z := by
        apply BalancedTensor.ext
        intro m n
        rfl
      exact congrArg (fun f => f y) hz
    exact congrArg (fun f => f x) h
  right_inv x := by
    let F := (forward k A B M N Z).comp (inverse k A B M N Z)
    have h : F = LinearMap.id := by
      apply BalancedTensor.ext
      intro m y
      have hm : F.comp (mk k A M (LeftTensor k B A N Z) m) =
          mk k A M (LeftTensor k B A N Z) m := by
        apply BalancedTensor.ext
        intro n z
        rfl
      exact congrArg (fun f => f y) hm
    exact congrArg (fun f => f x) h

end LittleFinitistic.BalancedAssociativity

end

end OAI
