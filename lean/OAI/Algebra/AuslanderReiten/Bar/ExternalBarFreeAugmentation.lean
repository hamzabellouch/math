import OAI.Algebra.AuslanderReiten.Bar.ExternalBarFreeCoordinate

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open CategoryTheory
open scoped TensorProduct
private theorem iso_cancel_pair {C : Type*} [Category C]
    {P Q R S V : C} (a : P ⟶ Q) (e : Q ≅ R) (f : R ≅ S) (b : Q ⟶ V) :
    (a ≫ e.hom ≫ f.hom) ≫ (f.inv ≫ e.inv ≫ b) = a ≫ b := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

universe u
variable (k A B M N : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]
variable [Module k M] [Module k N] [IsScalarTower k A M] [IsScalarTower k B N]
variable (e : M ≃ₗ[k] k) (f : N ≃ₗ[k] k)

def barCyclicCover :
    ModuleCat.of (A ⊗[k] B) (A ⊗[k] B) ⟶ canonicalTensorObject k A B M N :=
  (regularEquiv k A B).toModuleIso.inv ≫
    (canonicalTensorIso k A B A B).inv ≫
      mapHom k A B (ModuleCat.ofHom (ModuleBar.cyclicCover k A M e))
        (ModuleCat.ofHom (ModuleBar.cyclicCover k B N f))

private theorem factor_augmentation (R V : Type u) [Ring R] [Algebra k R]
    [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
    (a : V ≃ₗ[k] k) :
    (ModuleBar.freeCoordinate k R V a).toModuleIso.hom ≫
      ModuleCat.ofHom (ModuleBar.cyclicCover k R V a) =
        ModuleCat.ofHom (ModuleBar.differential k R V 0) := by
  apply ModuleCat.hom_ext
  exact ModuleBar.freeCoordinate_augmentation k R V a

theorem barFreeCoordinate_augmentation :
    barFreeCoordinate k A B M N e f ≫ barCyclicCover k A B M N e f =
      mapHom k A B (ModuleCat.ofHom (ModuleBar.differential k A M 0))
        (ModuleCat.ofHom (ModuleBar.differential k B N 0)) := by
  have h := iso_cancel_pair
    (mapHom k A B (ModuleBar.freeCoordinate k A M e).toModuleIso.hom
      (ModuleBar.freeCoordinate k B N f).toModuleIso.hom)
    (canonicalTensorIso k A B A B) (regularEquiv k A B).toModuleIso
    (mapHom k A B (ModuleCat.ofHom (ModuleBar.cyclicCover k A M e))
      (ModuleCat.ofHom (ModuleBar.cyclicCover k B N f)))
  have hcomp := (mapHom_comp k A B
    (ModuleBar.freeCoordinate k A M e).toModuleIso.hom
    (ModuleCat.ofHom (ModuleBar.cyclicCover k A M e))
    (ModuleBar.freeCoordinate k B N f).toModuleIso.hom
    (ModuleCat.ofHom (ModuleBar.cyclicCover k B N f))).symm
  exact h.trans (hcomp.trans (congrArg₂ (mapHom k A B)
    (factor_augmentation k A M e) (factor_augmentation k B N f)))

end ArExplicit.ExternalTensor

end

end OAI
