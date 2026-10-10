import OAI.Algebra.Finitistic.Bar.CoproductHomotopy
import OAI.Algebra.Finitistic.Bar.CoproductHomBijections
import Mathlib.Algebra.Homology.DerivedCategory.KProjective

namespace OAI
open CategoryTheory CategoryTheory.Limits HomologicalComplex
noncomputable section
namespace DerivedBar
universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasColimitsOfShape (Discrete ℕ) C] [HasDerivedCategory.{w} C]
  (F : Discrete ℕ ⥤ CochainComplex C ℤ) (s : Cocone F) (hs : IsColimit s)
  [s.pt.IsKProjective] [∀ r, (F.obj r).IsKProjective]

/-- An actual coproduct of K-projective cochain complexes with K-projective
coproduct object remains a coproduct in the genuine derived category. -/
def kProjectiveCoproductIsColimit : IsColimit (DerivedCategory.Q.mapCocone s) := by
  let H := HomotopyCategory.quotient C (.up ℤ)
  let hsH := homotopyCoproductIsColimit F s hs
  let hsD := mapCoproductOfHomBijections DerivedCategory.Qh (F ⋙ H) (H.mapCocone s) hsH
    (fun T => CochainComplex.IsKProjective.Qh_map_bijective s.pt T)
    (fun r T => CochainComplex.IsKProjective.Qh_map_bijective (F.obj r) T)
  letI : PreservesColimit F (H ⋙ DerivedCategory.Qh) :=
    preservesColimit_of_preserves_colimit_cocone hs hsD
  letI : PreservesColimit F (DerivedCategory.Q : CochainComplex C ℤ ⥤ _) :=
    preservesColimit_of_natIso F (DerivedCategory.quotientCompQhIso C)
  exact isColimitOfPreserves DerivedCategory.Q hs
end DerivedBar

end

end OAI
