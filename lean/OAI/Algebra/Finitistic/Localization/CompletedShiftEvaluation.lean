import OAI.Algebra.Finitistic.Localization.CompletedImageEvaluation

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Idempotents
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.QuadraticEncoding
universe u v w z
section General
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {D : Type w} [Category.{z} D] [Preadditive D] [IsIdempotentComplete D]
variable (F : C ⥤ D) [F.Additive]

/-- Commutation with any endofunctor extends uniquely across idempotent completion. -/
def completedCommutationIso (S : C ⥤ C) (T : D ⥤ D) (e : S ⋙ F ≅ F ⋙ T) :
    (functorExtension₂ C C).obj S ⋙ (functorExtension C D).obj F ≅
      (functorExtension C D).obj F ⋙ T := by
  let G := (functorExtension C D).obj F
  let S' := (functorExtension₂ C C).obj S
  let h : toKaroubi C ⋙ (S' ⋙ G) ≅ toKaroubi C ⋙ (G ⋙ T) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight ((functorExtension₂CompWhiskeringLeftToKaroubiIso C C).app S) G ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft S (completedExtensionFactors F) ≪≫ e ≪≫
      Functor.isoWhiskerRight (completedExtensionFactors F).symm T ≪≫
      Functor.associator _ _ _
  exact (whiskeringLeftObjToKaroubiFullyFaithful (C := C) (D := D)).preimageIso h
end General

variable {k : Type u} [Field k] {d t : ℕ} {P : Relations k d t}
variable {Y : Type v} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
variable (X : Representation P Y)

/-- This is the formal shift used by the native odd-double construction: shift
the underlying object and its idempotent. No shift coherence is assumed. -/
def completedDerivedShiftIso (n : ℤ) :
    (functorExtension₂ (BoundedQ P) (BoundedQ P)).obj (shiftFunctor (BoundedQ P) n) ⋙
      completedDerivedEvaluation X ≅
    completedDerivedEvaluation X ⋙ shiftFunctor (FiniteVectorDerived.{u,v} (k := k)) n :=
  completedCommutationIso (derivedQuotientEvaluation X) _ _
    ((derivedQuotientEvaluation X).commShiftIso n)

/-- In particular, every formal shift of U evaluates to the same shift of eY. -/
def completedShiftedSummandImageIso (r : PresentedAlgebra P) (hr : r*r=r) (n : ℤ) :
    (completedDerivedEvaluation X).obj
      (((functorExtension₂ (BoundedQ P) (BoundedQ P)).obj (shiftFunctor (BoundedQ P) n)).obj
        (quotientSummand r hr)) ≅ (evaluatedImageDerived X r)⟦n⟧ :=
  (completedDerivedShiftIso X n).app (quotientSummand r hr) ≪≫
    (shiftFunctor _ n).mapIso (completedSummandImageIso X r hr)
end LittleFinitistic.QuadraticEncoding

end

end OAI
