import OAI.Algebra.Finitistic.Localization.CompletedCornerEvaluation
import OAI.Algebra.Finitistic.Localization.CompletedShiftEvaluation

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Idempotents
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.QuadraticEncoding
universe u v
variable {k : Type u} [Field k] {d t : ℕ} {P : Relations k d t}
variable {Y : Type v} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
variable (X : Representation P Y) (e a : PresentedAlgebra P) (he : e*e=e)

/-- The same corner action evaluates correctly on every formal shift, including shift 3. -/
theorem completed_shifted_corner_square (n : ℤ) :
    (completedDerivedEvaluation X).map
      (((functorExtension₂ (BoundedQ P) (BoundedQ P)).obj (shiftFunctor (BoundedQ P) n)).map
        (quotientCornerEnd e a he)) ≫ (completedShiftedSummandImageIso X e he n).hom =
    (completedShiftedSummandImageIso X e he n).hom ≫ (evaluatedCornerEnd X e a)⟦n⟧' := by
  have hn := (completedDerivedShiftIso X n).hom.naturality (quotientCornerEnd e a he)
  have hm := congrArg (shiftFunctor (FiniteVectorDerived.{u,v} (k := k)) n).map
    (completed_corner_square X e a he)
  simp only [Functor.map_comp] at hm
  change _ ≫ ((completedDerivedShiftIso X n).hom.app (quotientSummand e he) ≫
    (shiftFunctor _ n).map (completedSummandImageIso X e he).hom) =
    ((completedDerivedShiftIso X n).hom.app (quotientSummand e he) ≫
    (shiftFunctor _ n).map (completedSummandImageIso X e he).hom) ≫ _
  rw [← Category.assoc]
  change (((functorExtension₂ (BoundedQ P) (BoundedQ P)).obj (shiftFunctor (BoundedQ P) n) ⋙
    completedDerivedEvaluation X).map (quotientCornerEnd e a he) ≫ _) ≫ _ = _
  rw [hn, Category.assoc]
  change _ ≫ ((shiftFunctor _ n).map ((completedDerivedEvaluation X).map (quotientCornerEnd e a he)) ≫ _) = _
  rw [hm, ← Category.assoc]
end LittleFinitistic.QuadraticEncoding

end

end OAI
