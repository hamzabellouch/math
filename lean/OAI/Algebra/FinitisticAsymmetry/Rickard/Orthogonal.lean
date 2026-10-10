import Mathlib
import OAI.Algebra.FinitisticAsymmetry.Model

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace LittleFinitistic.Rickard
universe u v t
variable {C : Type u} [Category.{v} C]

lemma leftOrthogonal_closed [HasZeroMorphisms C] (P : ObjectProperty C) (J : Type t) [Category J] :
    P.leftOrthogonal.IsClosedUnderColimitsOfShape J := by
  apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
  rintro _ ⟨F, hF⟩ Y f hY
  apply colimit.hom_ext
  intro j
  simpa using hF j (colimit.ι F j ≫ f) hY

section
variable [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

def perpendicular (X : C) : ObjectProperty C :=
  ((ObjectProperty.singleton X).shiftClosure ℤ).leftOrthogonal

instance perpendicular_isClosedUnderIsomorphisms (X : C) :
    (perpendicular X).IsClosedUnderIsomorphisms := inferInstanceAs
      (((ObjectProperty.singleton X).shiftClosure ℤ).leftOrthogonal.IsClosedUnderIsomorphisms)

instance perpendicular_isTriangulated (X : C) : (perpendicular X).IsTriangulated :=
  inferInstanceAs (((ObjectProperty.singleton X).shiftClosure ℤ).leftOrthogonal.IsTriangulated)

instance perpendicular_closed (X : C) (J : Type t) [Category J] :
    (perpendicular X).IsClosedUnderColimitsOfShape J := leftOrthogonal_closed _ J

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
lemma perpendicular_iff (X Y : C) : perpendicular X Y ↔
    ∀ (n : ℤ) (f : Y ⟶ X⟦n⟧), f = 0 := by
  constructor
  · intro h n f
    exact h f ⟨X,n,Iso.refl _, by simp⟩
  · intro h Z f hZ
    obtain ⟨X', n, e, he⟩ := hZ
    have he' : X = X' := by simpa using he
    subst X'
    apply (cancel_mono e.hom).mp
    simpa using h n (f ≫ e.hom)

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
lemma isZero_of_perpendicular_self (X : C) (hX : perpendicular X X) : IsZero X := by
  apply (IsZero.iff_id_eq_zero _).mpr
  exact hX (𝟙 X) ((ObjectProperty.singleton X).le_shiftClosure X (by simp))
end

variable {R : Type u} [Ring R]
local instance orthogonalHasDerivedCategory : HasDerivedCategory (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _

lemma not_generate_of_orthogonal
    (X : @DerivedCategory (ModuleCat.{u} R) _ _ (HasDerivedCategory.standard _))
    (hX : ¬ IsZero X)
    (hI : ∀ (M : ModuleCat.{u} R), Injective M →
      ∀ (n : ℤ) (f : (DerivedCategory.singleFunctor _ 0).obj M ⟶ X⟦n⟧), f = 0) :
    ¬ InjectivesGenerate R := by
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  intro h
  apply hX
  apply isZero_of_perpendicular_self
  apply h (perpendicular X) inferInstance inferInstance (fun I => inferInstance)
  intro M hM
  exact (perpendicular_iff X _).mpr (hI M hM)

end LittleFinitistic.Rickard

end

end OAI
