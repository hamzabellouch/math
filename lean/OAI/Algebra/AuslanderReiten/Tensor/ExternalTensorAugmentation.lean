import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorResolution
import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorCubicDifferential

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open CategoryTheory HomologicalComplex
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (M : ModuleCat.{u} A) (N : ModuleCat.{u} B)

theorem singleTotalZeroEquiv_insert (x : moduleObject k A B M N) :
    singleTotalZeroEquiv k A B M N
      (cubicInsert k A B ((ChainComplex.single₀ (ModuleCat A)).obj M)
        ((ChainComplex.single₀ (ModuleCat B)).obj N) 0 ⟨(0,0),rfl⟩ x) = x := by
  let e := termDirectSumEquiv k A B ((ChainComplex.single₀ (ModuleCat A)).obj M)
    ((ChainComplex.single₀ (ModuleCat B)).obj N) 0
  change (e (e.symm (DFinsupp.single ⟨(0,0),rfl⟩ x))) ⟨(0,0),rfl⟩ = x
  rw [LinearEquiv.apply_symm_apply]
  exact DFinsupp.single_eq_same

theorem singleTotalIso_inclusion :
    inclusion k A B ((ChainComplex.single₀ (ModuleCat A)).obj M)
      ((ChainComplex.single₀ (ModuleCat B)).obj N) 0 0 0 rfl ≫
        (singleTotalIso k A B M N).hom.f 0 = 𝟙 (moduleObject k A B M N) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change singleTotalZeroEquiv k A B M N
    ((inclusion k A B ((ChainComplex.single₀ (ModuleCat A)).obj M)
      ((ChainComplex.single₀ (ModuleCat B)).obj N) 0 0 0 rfl).hom x) = x
  rw [inclusion_eq_cubicInsert]
  exact singleTotalZeroEquiv_insert k A B M N x

variable {M N} (P : ProjectiveResolution M) (Q : ProjectiveResolution N)

theorem inclusion_augmentation :
    inclusion k A B P.complex Q.complex 0 0 0 rfl ≫ (augmentation k A B P Q).f 0 =
      mapHom k A B (P.π.f 0) (Q.π.f 0) := by
  unfold augmentation
  rw [HomologicalComplex.comp_f, ← Category.assoc]
  rw [show inclusion k A B P.complex Q.complex 0 0 0 rfl ≫
      (mapBifunctorMap P.π Q.π (bifunctor k A B) (ComplexShape.down ℕ)).f 0 =
    ((bifunctor k A B).map (P.π.f 0)).app (Q.complex.X 0) ≫
      ((bifunctor k A B).obj (((ChainComplex.single₀ (ModuleCat A)).obj M).X 0)).map (Q.π.f 0) ≫
        inclusion k A B ((ChainComplex.single₀ (ModuleCat A)).obj M)
          ((ChainComplex.single₀ (ModuleCat B)).obj N) 0 0 0 rfl from
      ι_mapBifunctorMap P.π Q.π (bifunctor k A B) (ComplexShape.down ℕ) 0 0 0 rfl]
  erw [Category.assoc, Category.assoc, singleTotalIso_inclusion, Category.comp_id]
  change mapHom k A B (P.π.f 0) (𝟙 _) ≫ mapHom k A B (𝟙 _) (Q.π.f 0) = _
  rw [← mapHom_comp, Category.comp_id, Category.id_comp]

theorem augmentation_insert (x : moduleObject k A B (P.complex.X 0) (Q.complex.X 0)) :
    (augmentation k A B P Q).f 0 (cubicInsert k A B P.complex Q.complex 0 ⟨(0,0),rfl⟩ x) =
      mapHom k A B (P.π.f 0) (Q.π.f 0) x := by
  have h := congrArg (fun f => f.hom x) (inclusion_augmentation k A B P Q)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, inclusion_eq_cubicInsert] at h
  convert! h using 1

end ArExplicit.ExternalTensor

end

end OAI
