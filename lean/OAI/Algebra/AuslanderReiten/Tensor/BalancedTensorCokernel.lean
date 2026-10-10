import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorCategory
import OAI.Algebra.AuslanderReiten.Cones.CochainCokernel

namespace OAI

noncomputable section
namespace ArExplicit.BalancedTensor
open CategoryTheory CompleteComparison
universe u
variable {k R S F : Type u} [Field k] [Ring R] [Ring S] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F] [Module S F]
variable [IsScalarTower k Rᵐᵒᵖ F]
variable [SMulCommClass k S F] [SMulCommClass S Rᵐᵒᵖ F]
variable [Module.Finite Rᵐᵒᵖ F] [Module.Projective Rᵐᵒᵖ F]
variable {L M : Type u} [AddCommGroup L] [AddCommGroup M]
variable [Module k L] [Module k M] [Module R L] [Module R M]
variable [IsScalarTower k R L] [IsScalarTower k R M]
variable [SMulCommClass k R M]

def cokernelEquiv (d : L →ₗ[R] M) :
    (BalancedTensor k R F M ⧸ LinearMap.range (mapRight (k := k) (F := F) (S := S) d)) ≃ₗ[S]
      BalancedTensor k R F (M ⧸ LinearMap.range d) :=
  (mapRight_exact (k := k) (F := F) (S := S) d (LinearMap.range d).mkQ
    (LinearMap.exact_map_mkQ_range d)).linearEquivOfSurjective
      (mapRight_surjective (k := k) (F := F) (S := S) _ (Submodule.mkQ_surjective _))

theorem cokernelEquiv_mk (d : L →ₗ[R] M) (x : BalancedTensor k R F M) :
    cokernelEquiv (k := k) (F := F) (S := S) d (Submodule.Quotient.mk x) =
      mapRight (k := k) (F := F) (S := S) (LinearMap.range d).mkQ x := by
  apply (cokernelEquiv (k := k) (F := F) (S := S) d).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  exact (Function.Exact.linearEquivOfSurjective_symm_apply _ _ x).symm

@[simp] theorem cokernelEquiv_mk_tmul (d : L →ₗ[R] M) (f : F) (m : M) :
    cokernelEquiv (k := k) (F := F) (S := S) d (Submodule.Quotient.mk (tmul f m)) =
      tmul f (Submodule.Quotient.mk m) := by
  rw [cokernelEquiv_mk, mapRight_tmul]
  rfl

attribute [local instance] moduleCatBaseModule moduleCatBaseTower

def cochainCokernelEquiv (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainCokernel (((functor (k := k) (R := R) (S := S) (F := F)).mapHomologicalComplex _).obj P) ≃ₗ[S]
      BalancedTensor k R F (CochainCokernel P) :=
  cokernelEquiv (k := k) (F := F) (S := S) (P.d (-1) 0).hom

@[simp] theorem cochainCokernelEquiv_mk_tmul
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (f : F) (x : P.X 0) :
    cochainCokernelEquiv (k := k) (F := F) (S := S) P
      (Submodule.Quotient.mk (tmul f x)) = tmul f (Submodule.Quotient.mk x) :=
  cokernelEquiv_mk_tmul (k := k) (F := F) (S := S) (P.d (-1) 0).hom f x

variable {G : Type u} [AddCommGroup G] [Module k G] [Module Rᵐᵒᵖ G] [Module S G]
variable [IsScalarTower k Rᵐᵒᵖ G]
variable [SMulCommClass k S G] [SMulCommClass S Rᵐᵒᵖ G]
variable [Module.Finite Rᵐᵒᵖ G] [Module.Projective Rᵐᵒᵖ G]

theorem cochainCokernelEquiv_natural
    (a : F →ₗ[Rᵐᵒᵖ] G) (ha : ∀ (s : S) f, a (s • f) = s • a f)
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (z : CochainCokernel (((functor (k := k) (R := R) (S := S) (F := F)).mapHomologicalComplex _).obj P)) :
    cochainCokernelEquiv (k := k) (F := G) (S := S) P
      (cochainCokernelMap (complexMap (k := k) a ha P) z) =
    mapLeft (k := k) (M := CochainCokernel P) a
      (cochainCokernelEquiv (k := k) (F := F) (S := S) P z) := by
  obtain ⟨x,rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range (((((functor (k := k) (R := R) (S := S) (F := F)).mapHomologicalComplex _).obj P).d (-1) 0).hom)) z
  induction x using induction_on with
  | zero =>
    repeat' erw [map_zero]
  | add x y hx hy =>
    repeat' erw [map_add]
    exact congrArg₂ (· + ·) hx hy
  | tmul f m =>
    erw [cochainCokernelMap_mk]
    change cochainCokernelEquiv (k := k) (F := G) (S := S) P
        (Submodule.Quotient.mk (tmul (a f) m)) = _
    erw [cochainCokernelEquiv_mk_tmul]

end ArExplicit.BalancedTensor

end

end OAI
