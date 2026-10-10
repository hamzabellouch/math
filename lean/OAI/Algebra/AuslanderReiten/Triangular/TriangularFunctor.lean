import OAI.Algebra.AuslanderReiten.Triangular.TriangularInduction
import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorPi

namespace OAI

noncomputable section

namespace ArExplicit.TriangularInduction

variable {k R F : Type*} [CommRing k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]
variable {M N L : Type*}
variable [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]
variable [AddCommGroup N] [Module k N] [Module R N] [IsScalarTower k R N]
variable [AddCommGroup L] [Module k L] [Module R L] [IsScalarTower k R L]

def eMap (f : M →ₗ[R] N) : TriangularE k R F M →ₗ[Triangular R F] TriangularE k R F N := eHom f

def jMap (f : M →ₗ[R] N) : TriangularJ k R F M →ₗ[Triangular R F] TriangularJ k R F N := jHom f

omit [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F] in
@[simp] theorem eMap_top (f : M →ₗ[R] N) (x : TriangularE k R F M) :
    (eMap f x).top = f x.top := rfl

omit [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F] in
@[simp] theorem eMap_bottom (f : M →ₗ[R] N) (x : TriangularE k R F M) :
    (eMap f x).bottom = BalancedTensor.mapRight (S := R) f x.bottom := rfl

omit [Algebra k R] [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F]
  [SMulCommClass k Rᵐᵒᵖ F] [Module k M] [IsScalarTower k R M]
  [Module k N] [IsScalarTower k R N] in
@[simp] theorem jMap_bottom (f : M →ₗ[R] N) (x : TriangularJ k R F M) :
    (jMap f x).bottom = f x.bottom := rfl

@[simp] theorem eMap_id : eMap (k := k) (F := F) (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  apply eHomEquiv.injective
  ext m
  rfl

@[simp] theorem eMap_comp (f : M →ₗ[R] N) (g : N →ₗ[R] L) :
    eMap (k := k) (F := F) (g.comp f) = (eMap g).comp (eMap f) := by
  apply eHomEquiv.injective
  ext m
  rfl

@[simp] theorem jMap_id : jMap (k := k) (F := F) (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  apply jHomEquiv.injective
  ext m
  rfl

omit [Module k M] [IsScalarTower k R M] [Module k N] [IsScalarTower k R N] in
@[simp] theorem jMap_comp (f : M →ₗ[R] N) (g : N →ₗ[R] L) :
    jMap (k := k) (F := F) (g.comp f) = (jMap g).comp (jMap f) := by
  apply jHomEquiv.injective
  ext m
  rfl

@[simp] theorem eMap_zero : eMap (k := k) (F := F) (0 : M →ₗ[R] N) = 0 := by
  apply eHomEquiv.injective
  ext m
  rfl

omit [Module k M] [IsScalarTower k R M] in
@[simp] theorem jMap_zero : jMap (k := k) (F := F) (0 : M →ₗ[R] N) = 0 := by
  apply jHomEquiv.injective
  ext m
  rfl

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

def ePi : TriangularE k R F (ι → M) ≃ₗ[Triangular R F] (ι → TriangularE k R F M) where
  toFun x i := ⟨x.top i, BalancedTensor.piRight (S := R) x.bottom i⟩
  invFun y := ⟨fun i => (y i).top, (BalancedTensor.piRight (S := R)).symm (fun i => (y i).bottom)⟩
  left_inv x := by ext <;> simp
  right_inv y := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_smul' a x := by
    ext i
    · rfl
    · change BalancedTensor.piRight (S := R)
          (BalancedTensor.tmul a.off x.top + a.bottom • x.bottom) i =
        BalancedTensor.tmul a.off (x.top i) + a.bottom • BalancedTensor.piRight (S := R) x.bottom i
      simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply]
      rfl

def jPi : TriangularJ k R F (ι → M) ≃ₗ[Triangular R F] (ι → TriangularJ k R F M) where
  toFun x i := ⟨0, x.bottom i⟩
  invFun y := ⟨0, fun i => (y i).bottom⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl
  map_add' x y := by ext; rfl
  map_smul' a x := by ext; simp

end ArExplicit.TriangularInduction

end

end OAI
