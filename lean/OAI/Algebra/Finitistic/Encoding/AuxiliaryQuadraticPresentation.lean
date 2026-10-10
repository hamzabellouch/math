import OAI.Algebra.Finitistic.Encoding.QuadraticPresentation
import OAI.Algebra.Finitistic.Selection.AuxiliaryGroupAlgebraPresentation

namespace OAI
noncomputable section
namespace LittleFinitistic.QuadraticPresentation

open GroupAlgebraPresentation in
/-- The Section 3 conversion applied to the exact Section 2 complex group algebra. -/
theorem auxiliaryGroupAlgebra_hasFiniteQuadraticPresentation :
    HasFiniteQuadraticPresentation ℂ (MonoidAlgebra ℂ Presentation.AuxiliaryGroup) :=
  finite_presentation_to_quadratic ℂ auxiliaryGroupAlgebra_hasFinitePresentation

abbrev AuxiliaryOldLetter := GroupAlgebraPresentation.Letter FinitePresentation.SeedGenerator
abbrev AuxiliaryOldEquation := GroupAlgebraPresentation.EquationIndex
  FinitePresentation.SeedGenerator FinitePresentation.finiteRelators

def auxiliaryOriginalRelation (i : AuxiliaryOldEquation) : FreeAlgebra ℂ AuxiliaryOldLetter :=
  GroupAlgebraPresentation.equation ℂ FinitePresentation.SeedGenerator
    FinitePresentation.finiteRelators i - 1

def auxiliaryWordBound : ℕ :=
  Classical.choose (exists_word_bound ℂ AuxiliaryOldLetter auxiliaryOriginalRelation)

theorem auxiliaryWordBound_spec (i : AuxiliaryOldEquation) (w : FreeMonoid AuxiliaryOldLetter)
    (hw : w ∈ (coefficients ℂ AuxiliaryOldLetter (auxiliaryOriginalRelation i)).support) :
    w.toList.length ≤ auxiliaryWordBound :=
  Classical.choose_spec (exists_word_bound ℂ AuxiliaryOldLetter auxiliaryOriginalRelation) i w hw

abbrev AuxiliaryLetter := Letter AuxiliaryOldLetter auxiliaryWordBound
abbrev AuxiliaryEquation := EquationIndex AuxiliaryOldLetter auxiliaryWordBound (κ := AuxiliaryOldEquation)

def auxiliaryRelation : AuxiliaryEquation → FreeAlgebra ℂ AuxiliaryLetter :=
  relation ℂ AuxiliaryOldLetter auxiliaryOriginalRelation auxiliaryWordBound

instance : Finite AuxiliaryLetter := inferInstanceAs (Finite (Letter AuxiliaryOldLetter auxiliaryWordBound))
instance : Finite AuxiliaryEquation := inferInstanceAs
  (Finite (EquationIndex AuxiliaryOldLetter auxiliaryWordBound (κ := AuxiliaryOldEquation)))

theorem auxiliaryRelation_degree (i : AuxiliaryEquation) :
    auxiliaryRelation i ∈ degreeLE ℂ AuxiliaryLetter 2 :=
  relation_degree ℂ AuxiliaryOldLetter auxiliaryOriginalRelation auxiliaryWordBound i

/-- Concrete quadratic quotient and actual algebra equivalence, retaining the
proved stable group's generators and relators and eliminating its word auxiliaries. -/
def auxiliaryQuadraticEquiv : Original ℂ AuxiliaryLetter auxiliaryRelation ≃ₐ[ℂ]
    MonoidAlgebra ℂ Presentation.AuxiliaryGroup :=
  (quadraticEquiv ℂ AuxiliaryOldLetter auxiliaryOriginalRelation auxiliaryWordBound
    auxiliaryWordBound_spec).trans GroupAlgebraPresentation.auxiliaryGroupAlgebraZeroEquiv

end LittleFinitistic.QuadraticPresentation

end

end OAI
