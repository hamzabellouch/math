import OAI.Algebra.AuslanderReiten.Triangular.Triangular
import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorUnit

namespace OAI

namespace ArExplicit

variable (k R F M N : Type*) [CommRing k] [Ring R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [AddCommGroup M] [Module k M] [Module R M]
variable [AddCommGroup N] [Module R N]

@[ext] structure TriangularModule (φ : BalancedTensor k R F M →ₗ[R] N) where
  top : M
  bottom : N

namespace TriangularModule

variable {k R F M N}
variable (φ : BalancedTensor k R F M →ₗ[R] N)

def coordinates : TriangularModule k R F M N φ ≃ M × N where
  toFun x := (x.top, x.bottom)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup (TriangularModule k R F M N φ) := (coordinates φ).addCommGroup

def coordinateAddEquiv : TriangularModule k R F M N φ ≃+ M × N where
  __ := coordinates φ
  map_add' _ _ := rfl

@[simp] theorem top_add (x y : TriangularModule k R F M N φ) : (x + y).top = x.top + y.top := rfl
@[simp] theorem bottom_add (x y : TriangularModule k R F M N φ) :
    (x + y).bottom = x.bottom + y.bottom := rfl
@[simp] theorem top_zero : (0 : TriangularModule k R F M N φ).top = 0 := rfl
@[simp] theorem bottom_zero : (0 : TriangularModule k R F M N φ).bottom = 0 := rfl

instance : SMul (Triangular R F) (TriangularModule k R F M N φ) :=
  ⟨fun a x => ⟨a.top • x.top, φ (BalancedTensor.tmul a.off x.top) + a.bottom • x.bottom⟩⟩

@[simp] theorem top_smul (a : Triangular R F) (x : TriangularModule k R F M N φ) :
    (a • x).top = a.top • x.top := rfl
@[simp] theorem bottom_smul (a : Triangular R F) (x : TriangularModule k R F M N φ) :
    (a • x).bottom = φ (BalancedTensor.tmul a.off x.top) + a.bottom • x.bottom := rfl

instance : Module (Triangular R F) (TriangularModule k R F M N φ) where
  one_smul x := by ext <;> simp
  mul_smul a b x := by
    ext
    · exact mul_smul a.top b.top x.top
    · simp only [bottom_smul, top_smul, Triangular.off_mul, Triangular.bottom_mul,
        BalancedTensor.add_tmul, BalancedTensor.balance, map_add, mul_smul, smul_add]
      rw [← BalancedTensor.smul_tmul, φ.map_smul]
      abel
  smul_add a x y := by
    ext <;> simp [BalancedTensor.tmul_add, smul_add, add_add_add_comm]
  smul_zero a := by ext <;> simp
  add_smul a b x := by
    ext <;> simp [BalancedTensor.add_tmul, add_smul, add_add_add_comm]
  zero_smul x := by ext <;> simp

section Scalars

variable [Module k N]

instance : Module k (TriangularModule k R F M N φ) := (coordinateAddEquiv φ).module k

@[simp] theorem top_scalar (c : k) (x : TriangularModule k R F M N φ) :
    (c • x).top = c • x.top := rfl
@[simp] theorem bottom_scalar (c : k) (x : TriangularModule k R F M N φ) :
    (c • x).bottom = c • x.bottom := rfl

variable [Algebra k R] [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F]
variable [SMulCommClass k Rᵐᵒᵖ F]
variable [IsScalarTower k R M] [IsScalarTower k R N]

instance : IsScalarTower k (Triangular R F) (TriangularModule k R F M N φ) where
  smul_assoc c a x := by
    ext
    · exact smul_assoc c a.top x.top
    · simp only [bottom_smul, Triangular.off_smul, Triangular.bottom_smul,
        bottom_scalar, BalancedTensor.scalar_tmul, LinearMap.map_smul_of_tower, smul_assoc, smul_add]

instance [SMulCommClass k R M] [SMulCommClass k R N] :
    SMulCommClass k (Triangular R F) (TriangularModule k R F M N φ) where
  smul_comm c a x := by
    ext
    · exact smul_comm c a.top x.top
    · simp only [bottom_scalar, bottom_smul, top_scalar, BalancedTensor.tmul_scalar,
        LinearMap.map_smul_of_tower, smul_add, smul_comm c a.bottom]

def coordinateLinearEquiv : TriangularModule k R F M N φ ≃ₗ[k] M × N :=
  (coordinateAddEquiv φ).linearEquiv k

instance [Module.Finite k M] [Module.Finite k N] :
    Module.Finite k (TriangularModule k R F M N φ) :=
  Module.Finite.equiv (coordinateLinearEquiv φ).symm

end Scalars

end TriangularModule
end ArExplicit

end OAI
