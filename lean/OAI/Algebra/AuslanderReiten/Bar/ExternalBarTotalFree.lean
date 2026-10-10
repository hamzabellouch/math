import OAI.Algebra.AuslanderReiten.Bar.ExternalBarFreeAugmentation
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorAugmentation

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B M N : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]
variable [Module k M] [Module k N] [IsScalarTower k A M] [IsScalarTower k B N] [CharP k 2]
variable (e : M ≃ₗ[k] k) (f : N ≃ₗ[k] k)

def barTotalFreeCoordinate :
    (complex k A B (ModuleBar.nativeResolution k A M).complex
      (ModuleBar.nativeResolution k B N).complex).X 0 ⟶
        ModuleCat.of (A ⊗[k] B) (A ⊗[k] B) :=
  ModuleCat.ofHom (bottomProjection k A B (ModuleBar.nativeResolution k A M).complex
    (ModuleBar.nativeResolution k B N).complex 0) ≫ barFreeCoordinate k A B M N e f

theorem inclusion_barTotalFreeCoordinate :
    inclusion k A B (ModuleBar.nativeResolution k A M).complex
      (ModuleBar.nativeResolution k B N).complex 0 0 0 rfl ≫
        barTotalFreeCoordinate k A B M N e f = barFreeCoordinate k A B M N e f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change barFreeCoordinate k A B M N e f
    (bottomProjection k A B (ModuleBar.nativeResolution k A M).complex
      (ModuleBar.nativeResolution k B N).complex 0
      ((inclusion k A B (ModuleBar.nativeResolution k A M).complex
        (ModuleBar.nativeResolution k B N).complex 0 0 0 rfl).hom x)) = _
  rw [inclusion_eq_cubicInsert, bottomProjection_bottom]
  rfl

theorem barTotalFreeCoordinate_augmentation :
    barTotalFreeCoordinate k A B M N e f ≫ barCyclicCover k A B M N e f =
      (augmentation k A B (ModuleBar.nativeResolution k A M)
        (ModuleBar.nativeResolution k B N)).f 0 := by
  apply hom_ext k A B (ModuleBar.nativeResolution k A M).complex
    (ModuleBar.nativeResolution k B N).complex
  intro i j h
  have hi : i=0 := by omega
  have hj : j=0 := by omega
  subst i; subst j
  erw [← Category.assoc, inclusion_barTotalFreeCoordinate,
    barFreeCoordinate_augmentation k A B M N e f, inclusion_augmentation]
  rfl

end ArExplicit.ExternalTensor

end

end OAI
