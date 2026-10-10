import OAI.Algebra.AuslanderReiten.Triangular.TriangularHom
import Mathlib.Algebra.Module.PUnit

namespace OAI

namespace ArExplicit

variable (k R F : Type*) [CommRing k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable (M : Type*) [AddCommGroup M] [Module k M] [Module R M]

abbrev TriangularE := TriangularModule k R F M (BalancedTensor k R F M) LinearMap.id

variable (N : Type*) [AddCommGroup N] [Module R N]

abbrev TriangularJ := TriangularModule k R F PUnit.{1} N 0

namespace TriangularInduction

variable {k R F M N}
variable {M' N' : Type*} [AddCommGroup M'] [Module k M'] [Module R M']
variable [AddCommGroup N'] [Module R N']
variable {ψ : BalancedTensor k R F M' →ₗ[R] N'}
variable [IsScalarTower k R M] [IsScalarTower k R M']

def eHom (a : M →ₗ[R] M') :
    TriangularE k R F M →ₗ[Triangular R F] TriangularModule k R F M' N' ψ :=
  TriangularModule.hom a (ψ.comp (BalancedTensor.mapRight a)) (by intros; rfl)

def jHom (b : N →ₗ[R] N') :
    TriangularJ k R F N →ₗ[Triangular R F] TriangularModule k R F M' N' ψ :=
  TriangularModule.hom 0 b (by intros; simp)

theorem eHom_topMap
    (g : TriangularE k R F M →ₗ[Triangular R F] TriangularModule k R F M' N' ψ) :
    eHom (TriangularModule.topMap g) = g := by
  apply TriangularModule.hom_ext
  · ext m; rfl
  · apply BalancedTensor.leftHom_ext
    intro f m
    exact (TriangularModule.compatibility g f m).symm

omit [Algebra k R] [IsScalarTower k R M'] in
theorem jHom_bottomMap
    (g : TriangularJ k R F N →ₗ[Triangular R F] TriangularModule k R F M' N' ψ) :
    jHom (TriangularModule.bottomMap g) = g := by
  apply TriangularModule.hom_ext
  · apply Subsingleton.elim
  · ext n; rfl

variable [Module k N] [Module k N']
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F]
variable [SMulCommClass k Rᵐᵒᵖ F]
variable [IsScalarTower k R N] [IsScalarTower k R N']
variable [SMulCommClass k R M'] [SMulCommClass k R N']

def eHomEquiv :
    (TriangularE k R F M →ₗ[Triangular R F] TriangularModule k R F M' N' ψ) ≃ₗ[k]
      (M →ₗ[R] M') where
  toFun := TriangularModule.topMap
  invFun := eHom
  left_inv := eHom_topMap
  right_inv a := by ext m; rfl
  map_add' g h := by ext m; rfl
  map_smul' c g := by ext m; rfl

def jHomEquiv :
    (TriangularJ k R F N →ₗ[Triangular R F] TriangularModule k R F M' N' ψ) ≃ₗ[k]
      (N →ₗ[R] N') where
  toFun := TriangularModule.bottomMap
  invFun := jHom
  left_inv := jHom_bottomMap
  right_inv a := by ext n; rfl
  map_add' g h := by ext n; rfl
  map_smul' c g := by ext n; rfl

theorem hom_E_J_eq_zero (g : TriangularE k R F M →ₗ[Triangular R F] TriangularJ k R F N) :
    g = 0 := by
  apply eHomEquiv.injective
  exact Subsingleton.elim _ _

end TriangularInduction
end ArExplicit

end OAI
