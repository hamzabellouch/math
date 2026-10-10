import OAI.Algebra.AuslanderReiten.Modules.TwistedBimodule
import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorFunctor

namespace OAI

namespace ArExplicit

@[ext] structure TwistedLeftModule (k R : Type*) [CommRing k] [Ring R] [Algebra k R]
    (σ : R ≃ₐ[k] R) (M : Type*) where
  value : M

namespace TwistedLeftModule

variable {k R M : Type*} [CommRing k] [Ring R] [Algebra k R]
variable [AddCommGroup M] [Module k M] [Module R M]
variable [IsScalarTower k R M] [SMulCommClass k R M]
variable (σ : R ≃ₐ[k] R)

def coordinates : TwistedLeftModule k R σ M ≃ M where
  toFun := value
  invFun := TwistedLeftModule.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup (TwistedLeftModule k R σ M) := (coordinates σ).addCommGroup
instance : Module k (TwistedLeftModule k R σ M) := (coordinates σ).addEquiv.module k
instance : SMul R (TwistedLeftModule k R σ M) := ⟨fun r x => ⟨σ.symm r • x.value⟩⟩

omit [Module k M] [Module R M] [IsScalarTower k R M] [SMulCommClass k R M] in
@[simp] theorem value_zero : (0 : TwistedLeftModule k R σ M).value = 0 := rfl
omit [Module k M] [Module R M] [IsScalarTower k R M] [SMulCommClass k R M] in
@[simp] theorem value_add (x y : TwistedLeftModule k R σ M) :
    (x + y).value = x.value + y.value := rfl
omit [Module R M] [IsScalarTower k R M] [SMulCommClass k R M] in
@[simp] theorem value_scalar_smul (a : k) (x : TwistedLeftModule k R σ M) :
    (a • x).value = a • x.value := rfl
omit [Module k M] [IsScalarTower k R M] [SMulCommClass k R M] in
@[simp] theorem value_smul (r : R) (x : TwistedLeftModule k R σ M) :
    (r • x).value = σ.symm r • x.value := rfl

instance : Module R (TwistedLeftModule k R σ M) where
  one_smul x := by ext; simp
  mul_smul r s x := by ext; simp [mul_smul]
  smul_zero r := by ext; simp
  smul_add r x y := by ext; simp [smul_add]
  add_smul r s x := by ext; simp [add_smul]
  zero_smul x := by ext; simp

instance : IsScalarTower k R (TwistedLeftModule k R σ M) where
  smul_assoc a r x := by ext; simp [smul_assoc]

instance : SMulCommClass k R (TwistedLeftModule k R σ M) where
  smul_comm a r x := by ext; exact smul_comm a (σ.symm r) x.value

def scalarEquiv : TwistedLeftModule k R σ M ≃ₗ[k] M where
  __ := coordinates σ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance [Module.Finite k M] : Module.Finite k (TwistedLeftModule k R σ M) :=
  Module.Finite.equiv (scalarEquiv σ).symm

end TwistedLeftModule

namespace TwistedBimodule

variable {k R M : Type*} [CommRing k] [Ring R] [Algebra k R]
variable [AddCommGroup M] [Module k M] [Module R M]
variable [IsScalarTower k R M] [SMulCommClass k R M]
variable (σ : R ≃ₐ[k] R)

private def untwistBilinear : TwistedBimodule k R σ →ₗ[k] M →ₗ[k] TwistedLeftModule k R σ M where
  toFun f :=
    { toFun := fun m => ⟨σ.symm f.value • m⟩
      map_add' x y := by ext; exact smul_add _ _ _
      map_smul' a x := by ext; exact (smul_comm a (σ.symm f.value) x).symm }
  map_add' f g := by ext m; simp [add_smul]
  map_smul' a f := by ext m; simp [smul_assoc]

private theorem untwist_balanced (f : TwistedBimodule k R σ) (r : R) (m : M) :
    untwistBilinear σ (MulOpposite.op r • f) m = untwistBilinear σ f (r • m) := by
  apply TwistedLeftModule.ext
  change σ.symm (f.value * σ r) • m = σ.symm f.value • (r • m)
  simp [mul_smul]

private theorem untwist_left (r : R) (f : TwistedBimodule k R σ) (m : M) :
    untwistBilinear σ (r • f) m = r • untwistBilinear σ f m := by
  apply TwistedLeftModule.ext
  change σ.symm (r * f.value) • m = σ.symm r • (σ.symm f.value • m)
  simp [mul_smul]

def tensorUntwistMap : BalancedTensor k R (TwistedBimodule k R σ) M →ₗ[R]
    TwistedLeftModule k R σ M :=
  BalancedTensor.liftLeft (untwistBilinear σ) (untwist_balanced σ) (untwist_left σ)

@[simp] theorem tensorUntwistMap_tmul (f : TwistedBimodule k R σ) (m : M) :
    tensorUntwistMap σ (BalancedTensor.tmul f m) = ⟨σ.symm f.value • m⟩ := rfl

private def untwistInverse : TwistedLeftModule k R σ M →ₗ[k]
    BalancedTensor k R (TwistedBimodule k R σ) M :=
  (BalancedTensor.mk (⟨1⟩ : TwistedBimodule k R σ)).comp (TwistedLeftModule.scalarEquiv σ).toLinearMap

def tensorUntwist : BalancedTensor k R (TwistedBimodule k R σ) M ≃ₗ[R]
    TwistedLeftModule k R σ M where
  __ := tensorUntwistMap σ
  invFun := untwistInverse σ
  left_inv z := by
    induction z using BalancedTensor.induction_on with
    | zero => simp
    | add x y hx hy =>
      change untwistInverse σ (tensorUntwistMap σ (x + y)) = x + y
      rw [map_add, map_add]
      exact congrArg₂ (· + ·) hx hy
    | tmul f m =>
      change BalancedTensor.tmul (k := k) (R := R)
        (⟨1⟩ : TwistedBimodule k R σ) (σ.symm f.value • m) =
        BalancedTensor.tmul f m
      rw [← BalancedTensor.balance]
      congr 1
      apply TwistedBimodule.ext
      simp
  right_inv x := by
    apply TwistedLeftModule.ext
    change σ.symm 1 • x.value = x.value
    simp

end TwistedBimodule
end ArExplicit

end OAI
