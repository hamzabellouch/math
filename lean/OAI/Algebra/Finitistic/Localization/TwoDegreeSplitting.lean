import OAI.Algebra.Finitistic.Localization.TwoDegreeExtVanishing
import OAI.Algebra.Finitistic.Localization.SingleDegreeNaturality

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
attribute [local instance] HasDerivedCategory.standard HasExt.standard
namespace LittleFinitistic.TwoDegreeFormality
open QuadraticEncoding DerivedTruncation DerivedCategory
universe u v
variable {k : Type u} [Field k] {d t : ℕ} (P : Relations k d t)
abbrev C := ModuleCat.{max u v} (B P)
abbrev D := DerivedCategory (C.{u,v} P)
abbrev H (n : ℤ) (X : D.{u,v} P) := (homologyFunctor (C P) n).obj X
abbrev stalk (M : C.{u,v} P) := (singleFunctor (C P) 0).obj M
variable (X : D.{u,v} P) (hX : TwoDegrees X)

def upperIso : upper X ≅ stalk P (H P 0 X) := by
  haveI := upper_isLE X hX
  exact canonicalIso 0 (upper X) ≪≫ (singleFunctor (C P) 0).mapIso
    (upperHomologyIso X 0 (by omega)).symm

def lowerIso : lower X ≅ (stalk P (H P (-3) X))⟦(3 : ℤ)⟧ := by
  haveI := lower_isLE X hX
  haveI := lower_isGE X hX
  exact canonicalIso (-3) (lower X) ≪≫
    (singleFunctor (C P) (-3)).mapIso (lowerHomologyIso X (-3) (by omega)) ≪≫
      ((singleFunctors (C P)).shiftIso 3 (-3) 0 (by omega)).symm.app (H P (-3) X)

def lowerShiftIso : (lower X)⟦(1 : ℤ)⟧ ≅ (stalk P (H P (-3) X))⟦(4 : ℤ)⟧ :=
  (shiftFunctor (D P) (1 : ℤ)).mapIso (lowerIso P X hX) ≪≫
    (shiftFunctorAdd (D P) (3 : ℤ) (1 : ℤ)).symm.app (stalk P (H P (-3) X))

include hX in
/-- The connecting map of the actual truncation triangle vanishes by Ext^4=0. -/
theorem connecting_eq_zero : (triangle X).mor₃ = 0 := by
  have hz := shifted_hom_eq_zero P (H P 0 X) (H P (-3) X) 4 (by omega)
    ((upperIso P X hX).inv ≫ (triangle X).mor₃ ≫ (lowerShiftIso P X hX).hom)
  apply (cancel_epi (upperIso P X hX).inv).mp
  apply (cancel_mono (lowerShiftIso P X hX).hom).mp
  erw [Category.assoc, comp_zero, zero_comp]
  exact hz

/-- A splitting of the actual truncation triangle, retaining its inclusion and projection. -/
structure TruncationSplit where
  iso : X ≅ lower X ⊞ upper X
  inclusion : DerivedTruncation.inclusion X ≫ iso.hom = biprod.inl
  projection : DerivedTruncation.projection X = iso.hom ≫ biprod.snd

def truncationSplit : TruncationSplit P X := Classical.choice (by
  obtain ⟨e,hi,hp⟩ := exists_iso_binaryBiproduct_of_distTriang
    (triangle X) (distinguished X) (connecting_eq_zero P X hX)
  exact ⟨⟨e,hi,hp⟩⟩)

/-- Actual B-linear two-degree formality, with the manuscript's shift by three. -/
def splitIso : X ≅ stalk P (H P 0 X) ⊞ (stalk P (H P (-3) X))⟦(3 : ℤ)⟧ :=
  (truncationSplit P X hX).iso ≪≫ biprod.mapIso (lowerIso P X hX) (upperIso P X hX) ≪≫
    biprod.braiding _ _
end LittleFinitistic.TwoDegreeFormality

end

end OAI
