import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorComplete
import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorMapEquiv
import OAI.Algebra.AuslanderReiten.Cones.CochainCokernelIso
import OAI.Algebra.AuslanderReiten.Duality.FiniteStableResolutionIso

namespace OAI

noncomputable section
namespace ArExplicit.BalancedTensor
open CategoryTheory CompleteComparison
universe u
variable {k R F : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F] [Module R F]
variable [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [Module.Finite Rᵐᵒᵖ F] [Module.Projective Rᵐᵒᵖ F]
variable [Module.Finite R F] [Module.Projective R F]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (τ : FrobeniusTrace k R) (M N : FiniteLeftModule k R)

abbrev completeTensor :=
  (((functor (k := k) (R := R) (S := R) (F := F)).mapHomologicalComplex _).obj
    (M.completeCochain τ))

def tensorCokernelEquiv : CochainCokernel (completeTensor (F := F) τ M) ≃ₗ[R]
    BalancedTensor k R F M.carrier :=
  (cochainCokernelEquiv (k := k) (F := F) (S := R) (M.completeCochain τ)).trans
    (mapRightEquiv (k := k) (F := F) (S := R) (M.completeCochainCokernelEquiv τ))

omit [SMulCommClass k Rᵐᵒᵖ F] [Module.Finite R F] [Module.Projective R F] in
@[simp] theorem tensorCokernelEquiv_mk (f : F) (x : (M.completeCochain τ).X 0) :
    tensorCokernelEquiv (F := F) τ M (Submodule.Quotient.mk (tmul f x)) =
      tmul f (M.completeCochainCokernelEquiv τ (Submodule.Quotient.mk x)) := by
  rw [tensorCokernelEquiv, LinearEquiv.trans_apply,
    cochainCokernelEquiv_mk_tmul, mapRightEquiv_tmul]

omit [SMulCommClass k Rᵐᵒᵖ F] in
theorem completeTensor_totallyAcyclic : TotallyAcyclicCochain (completeTensor (F := F) τ M) := by
  let := τ.regular_injective
  exact complex_totallyAcyclic (M.completeCochain τ)
    (M.completeCochain_totallyAcyclic τ).toExactProjectiveCochain

def completeTensorIso (e : BalancedTensor k R F M.carrier ≃ₗ[R] N.carrier) :
    (HomotopyCategory.quotient _ _).obj (completeTensor (F := F) τ M) ≅
      (HomotopyCategory.quotient _ _).obj (N.completeCochain τ) :=
  rawCokernelHomotopyIso (completeTensor_totallyAcyclic (F := F) τ M)
    (N.completeCochain_totallyAcyclic τ)
    (((tensorCokernelEquiv (F := F) τ M).trans e).trans (N.completeCochainCokernelEquiv τ).symm)

variable {G : Type u} [AddCommGroup G] [Module k G] [Module Rᵐᵒᵖ G] [Module R G]
variable [IsScalarTower k Rᵐᵒᵖ G] [SMulCommClass k Rᵐᵒᵖ G]
variable [SMulCommClass k R G] [SMulCommClass R Rᵐᵒᵖ G]
variable [Module.Finite Rᵐᵒᵖ G] [Module.Projective Rᵐᵒᵖ G]
variable [Module.Finite R G] [Module.Projective R G]

omit [SMulCommClass k Rᵐᵒᵖ F] [Module.Finite R F] [Module.Projective R F] in
omit [SMulCommClass k Rᵐᵒᵖ G] [Module.Finite R G] [Module.Projective R G] in
theorem tensorCokernelEquiv_natural (a : F →ₗ[Rᵐᵒᵖ] G)
    (ha : ∀ (r : R) f, a (r • f) = r • a f)
    (z : CochainCokernel (completeTensor (F := F) τ M)) :
    tensorCokernelEquiv (F := G) τ M
      (cochainCokernelMap (complexMap (k := k) a ha (M.completeCochain τ)) z) =
    mapLeft (k := k) (M := M.carrier) a (tensorCokernelEquiv (F := F) τ M z) := by
  obtain ⟨x,rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range ((completeTensor (F := F) τ M).d (-1) 0).hom) z
  induction x using induction_on with
  | zero => repeat' erw [map_zero]
  | add x y hx hy =>
    repeat' erw [map_add]
    exact congrArg₂ (· + ·) hx hy
  | tmul f m =>
    erw [cochainCokernelMap_mk]
    change tensorCokernelEquiv (F := G) τ M (Submodule.Quotient.mk (tmul (a f) m)) = _
    erw [tensorCokernelEquiv_mk]

variable (N' : FiniteLeftModule k R)

omit [SMulCommClass k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ G] in
theorem completeTensorIso_natural
    (a : F →ₗ[Rᵐᵒᵖ] G) (ha : ∀ (r : R) f, a (r • f) = r • a f)
    (e : BalancedTensor k R F M.carrier ≃ₗ[R] N.carrier)
    (e' : BalancedTensor k R G M.carrier ≃ₗ[R] N'.carrier)
    (b : N.carrier →ₗ[R] N'.carrier)
    (hab : ∀ x, e' (mapLeft (k := k) (M := M.carrier) a x) = b (e x)) :
    (HomotopyCategory.quotient _ _).map (complexMap (k := k) a ha (M.completeCochain τ)) ≫
      (completeTensorIso τ M N' e').hom =
    (completeTensorIso τ M N e).hom ≫
      (HomotopyCategory.quotient _ _).map (FiniteLeftModule.resolutionMap τ b) := by
  apply rawCokernelHomotopyIso_natural
  rw [FiniteLeftModule.resolutionMap_cokernel]
  apply LinearMap.ext
  intro z
  change (N'.completeCochainCokernelEquiv τ).symm
      (e' (tensorCokernelEquiv (F := G) τ M
        (cochainCokernelMap (complexMap (k := k) a ha (M.completeCochain τ)) z))) =
    (N'.completeCochainCokernelEquiv τ).symm
      (b ((N.completeCochainCokernelEquiv τ)
        ((N.completeCochainCokernelEquiv τ).symm (e (tensorCokernelEquiv (F := F) τ M z)))))
  rw [tensorCokernelEquiv_natural, LinearEquiv.apply_symm_apply, hab]

end ArExplicit.BalancedTensor

end

end OAI
