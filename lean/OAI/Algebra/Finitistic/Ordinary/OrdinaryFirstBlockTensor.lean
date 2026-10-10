import OAI.Algebra.Finitistic.Ordinary.OrdinaryBlockModules
import OAI.Algebra.Finitistic.Ordinary.OrdinaryBalancedCongruence

namespace OAI
noncomputable section
namespace LittleFinitistic.OrdinarySimulation.FirstBlockTensor
universe u
variable (k L R O T Z : Type u) [Field k] [Ring L] [Ring R] [Algebra k L] [Algebra k R]
variable [AddCommGroup O] [Module k O] [Module R O] [Module Lᵐᵒᵖ O]
  [IsScalarTower k R O] [IsScalarTower k Lᵐᵒᵖ O] [SMulCommClass R Lᵐᵒᵖ O]
variable [AddCommGroup T] [Module k T] [Module L T] [Module Rᵐᵒᵖ T]
  [IsScalarTower k L T] [IsScalarTower k Rᵐᵒᵖ T] [SMulCommClass L Rᵐᵒᵖ T]
variable [AddCommGroup Z] [Module k Z] [Module L Z] [IsScalarTower k L Z]

abbrev source := LeftTensor k (L × R) (L × R) (OffDiagonal O T) (BlockModule.First k L R Z)
abbrev target := BlockModule.Second k L R (LeftTensor k L R O Z)

def forward : source k L R O T Z →ₗ[k] target k L R O Z :=
  BalancedTensor.lift ((BalancedTensor.mk k L O Z).compl₁₂
    (show OffDiagonal O T →ₗ[k] O from LinearMap.fst k O T)
    (show BlockModule.First k L R Z →ₗ[k] Z from LinearMap.id)) (by
      intro d x z
      exact BalancedTensor.balance (k := k) (A := L) (M := O) (N := Z) d.1 x.1 (show Z from z))

def inverse : target k L R O Z →ₗ[k] source k L R O T Z :=
  BalancedTensor.lift ((BalancedTensor.mk k (L × R) (OffDiagonal O T) (BlockModule.First k L R Z)).compl₁₂
    (show O →ₗ[k] OffDiagonal O T from LinearMap.inl k O T)
    (show Z →ₗ[k] BlockModule.First k L R Z from LinearMap.id)) (by
      intro a o z
      have h := BalancedTensor.balance (k := k) (A := L × R) (M := OffDiagonal O T)
        (N := BlockModule.First k L R Z) (a,0) (o,0) z
      change BalancedTensor.mk k (L × R) (OffDiagonal O T) (BlockModule.First k L R Z)
          (MulOpposite.op a • o,(0:Rᵐᵒᵖ) • (0:T)) (show BlockModule.First k L R Z from z) =
        BalancedTensor.mk k (L × R) (OffDiagonal O T) (BlockModule.First k L R Z) (o,0)
          (show BlockModule.First k L R Z from a • z) at h
      rw [smul_zero] at h
      exact h)

omit [Algebra k L] [Algebra k R] [Module R O] [IsScalarTower k R O]
  [IsScalarTower k Lᵐᵒᵖ O] [SMulCommClass R Lᵐᵒᵖ O] [Module L T]
  [IsScalarTower k L T] [IsScalarTower k Rᵐᵒᵖ T] [SMulCommClass L Rᵐᵒᵖ T]
  [IsScalarTower k L Z] in
theorem other_block_zero (t : T) (z : BlockModule.First k L R Z) :
    BalancedTensor.mk k (L × R) (OffDiagonal O T) (BlockModule.First k L R Z) (0,t) z = 0 := by
  have h := BalancedTensor.balance (k := k) (A := L × R) (M := OffDiagonal O T)
    (N := BlockModule.First k L R Z) (0,1) (0,t) z
  change BalancedTensor.mk k (L × R) (OffDiagonal O T) (BlockModule.First k L R Z)
      ((0:Lᵐᵒᵖ) • (0:O),(1:Rᵐᵒᵖ) • t) z =
    BalancedTensor.mk k (L × R) (OffDiagonal O T) (BlockModule.First k L R Z) (0,t) ((0:L) • (show Z from z)) at h
  erw [zero_smul, one_smul, zero_smul, map_zero] at h
  exact h

omit [Module R O] [IsScalarTower k R O] [IsScalarTower k Lᵐᵒᵖ O]
  [SMulCommClass R Lᵐᵒᵖ O] [Module L T] [IsScalarTower k L T]
  [IsScalarTower k Rᵐᵒᵖ T] [SMulCommClass L Rᵐᵒᵖ T] [IsScalarTower k L Z] in
theorem inverse_forward (x : source k L R O T Z) :
    inverse k L R O T Z (forward k L R O T Z x) = x := by
  let F := (inverse k L R O T Z).comp (forward k L R O T Z)
  have h : F = LinearMap.id := by
    apply BalancedTensor.ext
    intro x z
    change BalancedTensor.mk k (L × R) (OffDiagonal O T) (BlockModule.First k L R Z) (x.1,0) z =
      BalancedTensor.mk k (L × R) (OffDiagonal O T) (BlockModule.First k L R Z) x z
    let q := (BalancedTensor.mk k (L × R) (OffDiagonal O T) (BlockModule.First k L R Z)).flip z
    have hx : x = (x.1,0) + (0,x.2) := Prod.ext (add_zero _).symm (zero_add _).symm
    exact ((congrArg q hx).trans ((q.map_add _ _).trans
      ((congrArg (q (x.1,0) + ·) (other_block_zero k L R O T Z x.2 z)).trans (add_zero _)))).symm
  exact congrArg (fun f => f x) h

omit [Module R O] [IsScalarTower k R O] [IsScalarTower k Lᵐᵒᵖ O]
  [SMulCommClass R Lᵐᵒᵖ O] [Module L T] [IsScalarTower k L T]
  [IsScalarTower k Rᵐᵒᵖ T] [SMulCommClass L Rᵐᵒᵖ T] [IsScalarTower k L Z] in
theorem forward_inverse (x : target k L R O Z) :
    forward k L R O T Z (inverse k L R O T Z x) = x := by
  have h : (forward k L R O T Z).comp (inverse k L R O T Z) = LinearMap.id := by
    apply BalancedTensor.ext
    intro o z
    rfl
  exact congrArg (fun f => f x) h

/-- Tensor on the first block selects O and has its actual output on the second block. -/
def equivalence : source k L R O T Z ≃ₗ[L × R] target k L R O Z where
  toFun := forward k L R O T Z
  invFun := inverse k L R O T Z
  left_inv := inverse_forward k L R O T Z
  right_inv := forward_inverse k L R O T Z
  map_add' := (forward k L R O T Z).map_add
  map_smul' d x := by
    let F := forward k L R O T Z
    have h : F.comp (LeftTensor.action k (L × R) (L × R) (OffDiagonal O T)
        (BlockModule.First k L R Z) d) =
        (Algebra.lsmul k k (target k L R O Z) d).comp F := by
      apply BalancedTensor.ext
      intro x z
      rfl
    exact congrArg (fun f => f x) h

end LittleFinitistic.OrdinarySimulation.FirstBlockTensor

end

end OAI
