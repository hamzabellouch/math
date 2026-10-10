import OAI.Algebra.Finitistic.Selection.GroupAlgebraPresentation
import OAI.Algebra.Finitistic.Selection.FinitePresentation

namespace OAI
noncomputable section
namespace LittleFinitistic.GroupAlgebraPresentation

/-- Section 2's complex group algebra, for the exact auxiliary group supplied
by the manuscript. The stable finite model has 18 generators, including the
three redundant diagonal W generators killed by its relations. -/
def auxiliaryGroupAlgebraEquiv :
    PresentedAlgebra ℂ FinitePresentation.SeedGenerator FinitePresentation.finiteRelators ≃ₐ[ℂ]
      MonoidAlgebra ℂ Presentation.AuxiliaryGroup :=
  (quotientEquiv ℂ FinitePresentation.SeedGenerator FinitePresentation.finiteRelators).trans
    (MonoidAlgebra.domCongr ℂ ℂ FinitePresentation.presentationEquiv)

/-- Same explicit presentation expressed as polynomial zero relations. -/
def auxiliaryGroupAlgebraZeroEquiv :
    (zeroRelations ℂ FinitePresentation.SeedGenerator FinitePresentation.finiteRelators).Quotient ≃ₐ[ℂ]
      MonoidAlgebra ℂ Presentation.AuxiliaryGroup :=
  (zeroQuotientEquiv ℂ FinitePresentation.SeedGenerator FinitePresentation.finiteRelators).trans
    (MonoidAlgebra.domCongr ℂ ℂ FinitePresentation.presentationEquiv)

/-- The finite-presentation assertion for R = ℂ[G] in Section 2's proof of
Proposition selection. This is a NONCOMMUTATIVE unital algebra presentation. -/
theorem auxiliaryGroupAlgebra_hasFinitePresentation :
    HasFinitePresentation ℂ (MonoidAlgebra ℂ Presentation.AuxiliaryGroup) := by
  let := FinitePresentation.auxiliaryGroup_isFinitelyPresented
  exact groupAlgebra_hasFinitePresentation ℂ Presentation.AuxiliaryGroup

/-- Positive and negative letters for the stable finite model: 36 algebra generators. -/
theorem auxiliary_algebra_generator_count :
    Fintype.card (Letter FinitePresentation.SeedGenerator) = 36 := by
  simp [Letter, Fintype.card_prod, FinitePresentation.seedGenerator_card]
end LittleFinitistic.GroupAlgebraPresentation

end

end OAI
