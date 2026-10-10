import OAI.Algebra.Finitistic.Bar.IntegerDerivedMultibar

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.IntegerExtensionFunctor
universe u
variable {B : Type u} [Ring B]
variable (F : ModuleCat.{u} B ⥤ ModuleCat.{u} B) [F.Additive]
variable (Z : ChainComplex (ModuleCat.{u} B) ℕ)
local notation "c" => ComplexShape.down ℕ
local notation "e" => ComplexShape.embeddingDownNat

/-- Additive functors preserve the zero components added by integer extension. -/
def termIso : (o : Option ℕ) → F.obj (HomologicalComplex.extend.X Z o) ≅
    HomologicalComplex.extend.X ((F.mapHomologicalComplex c).obj Z) o
  | none => (F.map_isZero (isZero_zero _)).iso (isZero_zero _)
  | some _ => Iso.refl _

theorem termIso_d (o o' : Option ℕ) :
    (termIso F Z o).hom ≫ HomologicalComplex.extend.d ((F.mapHomologicalComplex c).obj Z) o o' =
      F.map (HomologicalComplex.extend.d Z o o') ≫ (termIso F Z o').hom := by
  cases o <;> cases o' <;>
    simp [termIso,HomologicalComplex.extend.d,HomologicalComplex.extend.X] <;>
    erw [Functor.map_zero] <;> (try erw [comp_zero]) <;> (try erw [zero_comp])

/-- Applying an additive module functor commutes with the actual n ↦ -n zero extension. -/
def complexIso : (F.mapHomologicalComplex (.up ℤ)).obj ((DerivedBar.integerExtension B).obj Z) ≅
    (DerivedBar.integerExtension B).obj ((F.mapHomologicalComplex c).obj Z) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => termIso F Z (ComplexShape.embeddingDownNat.r n))
    (by intro n m h; exact termIso_d F Z (ComplexShape.embeddingDownNat.r n) (ComplexShape.embeddingDownNat.r m))

variable {Z} {Z' : ChainComplex (ModuleCat.{u} B) ℕ}
theorem termIso_natural (f : Z ⟶ Z') (o : Option ℕ) :
    F.map (HomologicalComplex.extend.mapX f o) ≫ (termIso F Z' o).hom =
      (termIso F Z o).hom ≫
        HomologicalComplex.extend.mapX ((F.mapHomologicalComplex c).map f) o := by
  cases o <;> simp [termIso,HomologicalComplex.extend.mapX,HomologicalComplex.extend.X]
  erw [Functor.map_zero,comp_zero,zero_comp]

/-- Naturality holds on every chain map, including the added zero degrees. -/
def naturalIso : DerivedBar.integerExtension B ⋙ F.mapHomologicalComplex (.up ℤ) ≅
    F.mapHomologicalComplex c ⋙ DerivedBar.integerExtension B :=
  NatIso.ofComponents (complexIso F) (by
    intro Z Z' f
    apply HomologicalComplex.Hom.ext
    funext n
    exact termIso_natural F f (ComplexShape.embeddingDownNat.r n))
end LittleFinitistic.IntegerExtensionFunctor

end

end OAI
