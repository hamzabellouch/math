import OAI.Algebra.Finitistic.Ordinary.OrdinaryBlockModules
import OAI.Algebra.Finitistic.Ordinary.OrdinaryBalancedCongruence

namespace OAI
noncomputable section
namespace LittleFinitistic.OrdinarySimulation.SecondBlockTensor
universe u
variable (k L R O T Z : Type u) [Field k] [Ring L] [Ring R] [Algebra k L] [Algebra k R]
variable [AddCommGroup O] [Module k O] [Module R O] [Module Lᵐᵒᵖ O]
  [IsScalarTower k R O] [IsScalarTower k Lᵐᵒᵖ O] [SMulCommClass R Lᵐᵒᵖ O]
variable [AddCommGroup T] [Module k T] [Module L T] [Module Rᵐᵒᵖ T]
  [IsScalarTower k L T] [IsScalarTower k Rᵐᵒᵖ T] [SMulCommClass L Rᵐᵒᵖ T]
variable [AddCommGroup Z] [Module k Z] [Module R Z] [IsScalarTower k R Z]

abbrev source := LeftTensor k (L × R) (L × R) (OffDiagonal O T) (BlockModule.Second k L R Z)
abbrev target := BlockModule.First k L R (LeftTensor k R L T Z)

def forward : source k L R O T Z →ₗ[k] target k L R T Z :=
  BalancedTensor.lift ((BalancedTensor.mk k R T Z).compl₁₂
    (show OffDiagonal O T →ₗ[k] T from LinearMap.snd k O T)
    (show BlockModule.Second k L R Z →ₗ[k] Z from LinearMap.id)) (by
      intro d x z
      exact BalancedTensor.balance (k := k) (A := R) (M := T) (N := Z) d.2 x.2 (show Z from z))

def inverse : target k L R T Z →ₗ[k] source k L R O T Z :=
  BalancedTensor.lift ((BalancedTensor.mk k (L × R) (OffDiagonal O T) (BlockModule.Second k L R Z)).compl₁₂
    (show T →ₗ[k] OffDiagonal O T from LinearMap.inr k O T)
    (show Z →ₗ[k] BlockModule.Second k L R Z from LinearMap.id)) (by
      intro a t z
      have h := BalancedTensor.balance (k := k) (A := L × R) (M := OffDiagonal O T)
        (N := BlockModule.Second k L R Z) (0,a) (0,t) z
      change BalancedTensor.mk k (L × R) (OffDiagonal O T) (BlockModule.Second k L R Z)
          ((0:Lᵐᵒᵖ) • (0:O),MulOpposite.op a • t) (show BlockModule.Second k L R Z from z) =
        BalancedTensor.mk k (L × R) (OffDiagonal O T) (BlockModule.Second k L R Z) (0,t)
          (show BlockModule.Second k L R Z from a • z) at h
      rw [smul_zero] at h
      exact h)

omit [Algebra k L] [Algebra k R] [Module R O] [IsScalarTower k R O]
  [IsScalarTower k Lᵐᵒᵖ O] [SMulCommClass R Lᵐᵒᵖ O] [Module L T]
  [IsScalarTower k L T] [IsScalarTower k Rᵐᵒᵖ T] [SMulCommClass L Rᵐᵒᵖ T]
  [IsScalarTower k R Z] in
theorem other_block_zero (o : O) (z : BlockModule.Second k L R Z) :
    BalancedTensor.mk k (L × R) (OffDiagonal O T) (BlockModule.Second k L R Z) (o,0) z = 0 := by
  have h := BalancedTensor.balance (k := k) (A := L × R) (M := OffDiagonal O T)
    (N := BlockModule.Second k L R Z) (1,0) (o,0) z
  change BalancedTensor.mk k (L × R) (OffDiagonal O T) (BlockModule.Second k L R Z)
      ((1:Lᵐᵒᵖ) • o,(0:Rᵐᵒᵖ) • (0:T)) z =
    BalancedTensor.mk k (L × R) (OffDiagonal O T) (BlockModule.Second k L R Z) (o,0) ((0:R) • (show Z from z)) at h
  erw [one_smul, zero_smul, zero_smul, map_zero] at h
  exact h

omit [Module R O] [IsScalarTower k R O] [IsScalarTower k Lᵐᵒᵖ O]
  [SMulCommClass R Lᵐᵒᵖ O] [Module L T] [IsScalarTower k L T]
  [IsScalarTower k Rᵐᵒᵖ T] [SMulCommClass L Rᵐᵒᵖ T] [IsScalarTower k R Z] in
theorem inverse_forward (x : source k L R O T Z) :
    inverse k L R O T Z (forward k L R O T Z x) = x := by
  let F := (inverse k L R O T Z).comp (forward k L R O T Z)
  have h : F = LinearMap.id := by
    apply BalancedTensor.ext
    intro x z
    change BalancedTensor.mk k (L × R) (OffDiagonal O T) (BlockModule.Second k L R Z) (0,x.2) z =
      BalancedTensor.mk k (L × R) (OffDiagonal O T) (BlockModule.Second k L R Z) x z
    let q := (BalancedTensor.mk k (L × R) (OffDiagonal O T) (BlockModule.Second k L R Z)).flip z
    have hx : x = (x.1,0) + (0,x.2) := Prod.ext (add_zero _).symm (zero_add _).symm
    exact ((congrArg q hx).trans ((q.map_add _ _).trans
      ((congrArg (· + q (0,x.2)) (other_block_zero k L R O T Z x.1 z)).trans (zero_add _)))).symm
  exact congrArg (fun f => f x) h

omit [Module R O] [IsScalarTower k R O] [IsScalarTower k Lᵐᵒᵖ O]
  [SMulCommClass R Lᵐᵒᵖ O] [Module L T] [IsScalarTower k L T]
  [IsScalarTower k Rᵐᵒᵖ T] [SMulCommClass L Rᵐᵒᵖ T] [IsScalarTower k R Z] in
theorem forward_inverse (x : target k L R T Z) :
    forward k L R O T Z (inverse k L R O T Z x) = x := by
  have h : (forward k L R O T Z).comp (inverse k L R O T Z) = LinearMap.id := by
    apply BalancedTensor.ext
    intro t z
    rfl
  exact congrArg (fun f => f x) h

/-- Tensor on the second block selects T and has its actual output on the first block. -/
def equivalence : source k L R O T Z ≃ₗ[L × R] target k L R T Z where
  toFun := forward k L R O T Z
  invFun := inverse k L R O T Z
  left_inv := inverse_forward k L R O T Z
  right_inv := forward_inverse k L R O T Z
  map_add' := (forward k L R O T Z).map_add
  map_smul' d x := by
    let F := forward k L R O T Z
    have h : F.comp (LeftTensor.action k (L × R) (L × R) (OffDiagonal O T)
        (BlockModule.Second k L R Z) d) =
        (Algebra.lsmul k k (target k L R T Z) d).comp F := by
      apply BalancedTensor.ext
      intro x z
      rfl
    exact congrArg (fun f => f x) h

end LittleFinitistic.OrdinarySimulation.SecondBlockTensor

end

end OAI
