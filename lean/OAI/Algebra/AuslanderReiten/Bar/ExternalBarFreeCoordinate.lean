import OAI.Algebra.AuslanderReiten.Bar.ModuleBarFreeAugmentation
import OAI.Algebra.AuslanderReiten.Bar.ModuleBarNative
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorScalarPure
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorRegular
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorFunctor
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorBottom

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B M N : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]
variable [Module k M] [Module k N] [IsScalarTower k A M] [IsScalarTower k B N]
variable (e : M ≃ₗ[k] k) (f : N ≃ₗ[k] k)

def barFreeCoordinate :
    letI := moduleCatBaseModule (k := k) (R := A) (ModuleBar.moduleObject k A M 1)
    letI := moduleCatBaseModule (k := k) (R := B) (ModuleBar.moduleObject k B N 1)
    letI := moduleCatBaseTower (k := k) (R := A) (ModuleBar.moduleObject k A M 1)
    letI := moduleCatBaseTower (k := k) (R := B) (ModuleBar.moduleObject k B N 1)
    moduleObject k A B (ModuleBar.moduleObject k A M 1) (ModuleBar.moduleObject k B N 1) ⟶
      ModuleCat.of (A ⊗[k] B) (A ⊗[k] B) :=
  mapHom k A B (ModuleBar.freeCoordinate k A M e).toModuleIso.hom
    (ModuleBar.freeCoordinate k B N f).toModuleIso.hom ≫
    (canonicalTensorIso k A B A B).hom ≫ (regularEquiv k A B).toModuleIso.hom

theorem barFreeCoordinate_tmul
    (x : ModuleBar.moduleObject k A M 1) (y : ModuleBar.moduleObject k B N 1) :
    barFreeCoordinate k A B M N e f
      (canonicalTmul k A B (ModuleBar.moduleObject k A M 1)
        (ModuleBar.moduleObject k B N 1) x y) =
      ModuleBar.freeCoordinate k A M e x ⊗ₜ[k] ModuleBar.freeCoordinate k B N f y := by
  change regularEquiv k A B ((canonicalTensorIso k A B A B).hom
    (canonicalTmul k A B A B (ModuleBar.freeCoordinate k A M e x)
      (ModuleBar.freeCoordinate k B N f y))) = _
  rw [canonicalTensorIso_tmul]
  rfl

end ArExplicit.ExternalTensor

end

end OAI
