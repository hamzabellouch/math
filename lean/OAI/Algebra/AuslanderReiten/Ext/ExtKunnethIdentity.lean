import OAI.Algebra.AuslanderReiten.Ext.ExtKunnethClass
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorHomCubic
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorAugmentation
import OAI.Algebra.AuslanderReiten.Resolutions.ResolutionExtIdentity

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {X : ModuleCat.{u} A} {Y : ModuleCat.{u} B}
variable (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)
variable [∀ n, Module.Finite A (P.complex.X n)] [∀ n, Module.Finite B (Q.complex.X n)]

theorem elementary_augmentation :
    elementaryHom k A B P.complex Q.complex X Y 0 0 0 rfl (P.π.f 0).hom (Q.π.f 0).hom =
      ((projectiveResolution k A B P Q).π.f 0).hom := by
  apply cubic_hom_ext k A B P.complex Q.complex 0
  rintro ⟨⟨i,j⟩,hij⟩ x
  obtain rfl : i=0 := by omega
  obtain rfl : j=0 := by omega
  exact (elementary_cubicInsert_same k A B P.complex Q.complex X Y 0 0 0 rfl
    (P.π.f 0).hom (Q.π.f 0).hom x).trans (augmentation_insert k A B P Q x).symm

private theorem extMk_congr {R : Type u} [Ring R] {M N : ModuleCat.{u} R}
    (L : ProjectiveResolution M) {n : ℕ} (f g : L.complex.X n ⟶ N)
    (hf : L.complex.d (n+1) n ≫ f=0) (hg : L.complex.d (n+1) n ≫ g=0) (hfg : f=g) :
    L.extMk f (n+1) rfl hf = L.extMk g (n+1) rfl hg := by subst g; rfl

variable [HasDerivedCategory (ModuleCat.{u} A)] [HasDerivedCategory (ModuleCat.{u} B)]
variable [HasDerivedCategory (ModuleCat.{u} (A ⊗[k] B))]

theorem extKunnethEquiv_identity :
    extKunnethEquiv k A B P Q X Y 0 (Ext.mk₀ (𝟙 (moduleObject k A B X Y))) =
      (Pi.single ⟨(0,0),rfl⟩ (Ext.mk₀ (𝟙 X) ⊗ₜ[k] Ext.mk₀ (𝟙 Y)) :
        ∀ d : Diagonal 0, Ext X X d.val.1 ⊗[k] Ext Y Y d.val.2) := by
  have hf := congrArg ModuleCat.Hom.hom P.complex_d_comp_π_f_zero
  have hg := congrArg ModuleCat.Hom.hom Q.complex_d_comp_π_f_zero
  have he := extKunnethEquiv_elementary k A B P Q X Y 0 0 0 rfl
    (P.π.f 0).hom (Q.π.f 0).hom hf hg
  have hm := extMk_congr (projectiveResolution k A B P Q)
    (ModuleCat.ofHom (X := (complex k A B P.complex Q.complex).X 0)
      (Y := moduleObject k A B X Y)
      (elementaryHom k A B P.complex Q.complex X Y 0 0 0 rfl (P.π.f 0).hom (Q.π.f 0).hom))
    ((projectiveResolution k A B P Q).π.f 0)
    (ModuleCat.hom_ext (elementary_closed k A B P.complex Q.complex X Y 0 0 0 rfl
      (P.π.f 0).hom (Q.π.f 0).hom hf hg))
    (projectiveResolution k A B P Q).complex_d_comp_π_f_zero
    (ModuleCat.hom_ext (elementary_augmentation k A B P Q))
  erw [hm, ResolutionProducts.extMk_augmentation, ResolutionProducts.extMk_augmentation,
    ResolutionProducts.extMk_augmentation] at he
  exact he

end ArExplicit.ExternalTensor

end

end OAI
