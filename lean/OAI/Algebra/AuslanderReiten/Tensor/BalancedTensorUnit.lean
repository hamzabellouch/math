import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorMap

namespace OAI

namespace ArExplicit.BalancedTensor

variable {k R : Type*} [CommRing k] [Ring R] [Algebra k R]

section Left

variable {M : Type*} [AddCommGroup M] [Module k M] [Module R M]
variable [IsScalarTower k R M]

def leftAction : R →ₗ[k] M →ₗ[k] M where
  toFun r :=
    { toFun := fun m => r • m
      map_add' := smul_add r
      map_smul' := fun c m => smul_comm r c m }
  map_add' r s := by ext m; exact add_smul r s m
  map_smul' c r := by ext m; exact smul_assoc c r m

def lunitMap : BalancedTensor k R R M →ₗ[R] M :=
  liftLeft leftAction (by intro x r m; exact mul_smul x r m)
    (by intro s r m; exact mul_smul s r m)

@[simp] theorem lunitMap_tmul (r : R) (m : M) :
    lunitMap (tmul r m : BalancedTensor k R R M) = r • m := rfl

def lunitInv : M →ₗ[R] BalancedTensor k R R M where
  toFun m := tmul 1 m
  map_add' := tmul_add 1
  map_smul' r m := by
    change tmul (k := k) (R := R) 1 (r • m) = tmul (r * 1) m
    rw [mul_one]
    simpa using (balance (k := k) (R := R) (1 : R) r m).symm

def lunit : BalancedTensor k R R M ≃ₗ[R] M where
  __ := lunitMap (k := k) (R := R) (M := M)
  invFun := lunitInv
  right_inv m := by simp [lunitInv]
  left_inv z := by
    change lunitInv (lunitMap z) = z
    induction z using induction_on with
    | zero => simp
    | tmul r m =>
      change tmul (k := k) (R := R) 1 (r • m) = tmul r m
      simpa using (balance (k := k) (R := R) (1 : R) r m).symm
    | add x y hx hy => simp only [map_add, hx, hy]

@[simp] theorem lunit_tmul (r : R) (m : M) :
    lunit (tmul r m : BalancedTensor k R R M) = r • m := rfl

end Left

section Right

variable {F : Type*} [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F]
variable [IsScalarTower k Rᵐᵒᵖ F]

def rightAction : F →ₗ[k] R →ₗ[k] F where
  toFun f :=
    { toFun := fun r => MulOpposite.op r • f
      map_add' r s := by simp [add_smul]
      map_smul' c r := by simp [MulOpposite.op_smul, smul_assoc] }
  map_add' f g := by ext r; exact smul_add _ _ _
  map_smul' c f := by ext r; exact smul_comm _ _ _

def runitMap : BalancedTensor k R F R →ₗ[k] F :=
  lift rightAction (by
    intro f r s
    change MulOpposite.op s • MulOpposite.op r • f = MulOpposite.op (r * s) • f
    rw [MulOpposite.op_mul, mul_smul])

@[simp] theorem runitMap_tmul (f : F) (r : R) :
    runitMap (tmul f r : BalancedTensor k R F R) = MulOpposite.op r • f := rfl

def runit : BalancedTensor k R F R ≃ₗ[k] F where
  __ := runitMap (k := k) (R := R) (F := F)
  invFun f := tmul f 1
  right_inv f := by simp [runitMap_tmul]
  left_inv z := by
    change tmul (runitMap z) 1 = z
    induction z using induction_on with
    | zero => simp
    | tmul f r => simpa using (balance (k := k) (R := R) f r (1 : R))
    | add x y hx hy => simpa only [map_add, add_tmul] using congrArg₂ (· + ·) hx hy

@[simp] theorem runit_tmul (f : F) (r : R) :
    runit (tmul f r : BalancedTensor k R F R) = MulOpposite.op r • f := rfl

variable {S : Type*} [Ring S] [Module S F]
variable [SMulCommClass k S F] [SMulCommClass S Rᵐᵒᵖ F]

def runitLeft : BalancedTensor k R F R ≃ₗ[S] F where
  __ := (runit (k := k) (R := R) (F := F)).toAddEquiv
  map_smul' s z := by
    change runit (s • z) = s • runit z
    induction z using induction_on with
    | zero => simp
    | tmul f r => simpa only [smul_tmul, runit_tmul] using (smul_comm s (MulOpposite.op r) f).symm
    | add x y hx hy => simp only [smul_add, map_add] at *; rw [hx, hy]

end Right

end ArExplicit.BalancedTensor

end OAI
