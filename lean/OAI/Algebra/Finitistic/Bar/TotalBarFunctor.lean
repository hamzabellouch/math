import OAI.Algebra.Finitistic.Bar.TotalBarResolution

namespace OAI
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace DerivedBar
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
local instance (N : ModuleCat.{u} A) : Module k N := Module.compHom N (algebraMap k A)
local instance (N : ModuleCat.{u} A) : IsScalarTower k A N :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
local notation "c" => ComplexShape.down ℕ

/-- The total bar resolution is a functor on nonnegative chain complexes. -/
def barTotalFunctor : ChainComplex (ModuleCat.{u} A) ℕ ⥤ ChainComplex (ModuleCat.{u} A) ℕ :=
  (barFunctor k A).mapHomologicalComplex c ⋙
    HomologicalComplex₂.flipFunctor _ c c ⋙ HomologicalComplex₂.totalFunctor _ c c c

@[reassoc]
theorem ι_barTotalFunctor_map {Z W : ChainComplex (ModuleCat.{u} A) ℕ} (f : Z ⟶ W)
    (i q n : ℕ) (h : i+q=n) :
    (barBicomplex k A Z).ιTotal c i q n h ≫ ((barTotalFunctor k A).map f).f n =
      ModuleCat.ofHom (termMap k A (Z.X q) (W.X q) (f.f q).hom (i+1)) ≫
        (barBicomplex k A W).ιTotal c i q n h := by
  dsimp only [barTotalFunctor, Functor.comp_map, HomologicalComplex₂.totalFunctor]
  erw [HomologicalComplex₂.ιTotal_map]
  rfl

private theorem augmentation_zero_diagonal (Z : ChainComplex (ModuleCat.{u} A) ℕ) (n : ℕ)
    (h : 0 + n = n) :
    (barBicomplex k A Z).ιTotal c 0 n n h ≫ barTotalAugmentationF k A Z n =
      ModuleCat.ofHom (differential k A (Z.X n) 0) := by
  erw [ι_barTotalAugmentationF_zero, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, Category.comp_id]

/-- The augmentation is natural for all chain maps, not only quasi-isomorphisms. -/
def barTotalAugmentationNat : barTotalFunctor k A ⟶ 𝟭 _ where
  app Z := barTotalAugmentation k A Z
  naturality {Z W} f := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply HomologicalComplex₂.total.hom_ext (K := barBicomplex k A Z)
    intro i q h
    change i+q=n at h
    change (barBicomplex k A Z).ιTotal c i q n h ≫ ((barTotalFunctor k A).map f).f n ≫ barTotalAugmentationF k A W n =
      (barBicomplex k A Z).ιTotal c i q n h ≫ barTotalAugmentationF k A Z n ≫ f.f n
    erw [ι_barTotalFunctor_map_assoc]
    cases i with
    | zero =>
      have hq : q=n := by omega
      subst q
      erw [Category.assoc, augmentation_zero_diagonal k A W n h,
        ← Category.assoc, augmentation_zero_diagonal k A Z n h]
      exact ModuleCat.hom_ext (differential_natural k A (Z.X n) (W.X n) (f.f n).hom 0)
    | succ i =>
      erw [Category.assoc, ι_barTotalAugmentationF_succ k A W i q n h,
        ← Category.assoc, ι_barTotalAugmentationF_succ k A Z i q n h]
      simp only [zero_comp]
      exact comp_zero
end DerivedBar

end

end OAI
