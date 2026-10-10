import OAI.Algebra.Finitistic.Localization.VectorIdempotentCompleteness

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Idempotents
attribute [local instance] HasDerivedCategory.standard
namespace LittleFinitistic.QuadraticEncoding
open FiniteProjectiveHomotopy VectorComplexFormality
universe u v w z
section General
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {D : Type w} [Category.{z} D] [Preadditive D]
variable (F : C ⥤ D) [F.Additive]

instance karoubiExtensionAdditive : ((functorExtension₂ C D).obj F).Additive where
  map_add := by
    intro A B f g
    apply Karoubi.Hom.ext
    exact F.map_add

variable [IsIdempotentComplete D]

instance completedExtensionAdditive : ((functorExtension C D).obj F).Additive :=
  inferInstanceAs (((functorExtension₂ C D).obj F ⋙ (toKaroubiEquivalence D).inverse).Additive)

/-- The extension restricts to the original functor under the canonical embedding. -/
def completedExtensionFactors :
    toKaroubi C ⋙ (functorExtension C D).obj F ≅ F :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((functorExtension₂CompWhiskeringLeftToKaroubiIso C D).app F)
      (toKaroubiEquivalence D).inverse ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft F (toKaroubiEquivalence D).unitIso.symm ≪≫
    Functor.rightUnitor F
/-- An explicitly split evaluated idempotent identifies the value of the completion. -/
def completedExtensionImageIso (U : Karoubi C) (I : D)
    (π : F.obj U.X ⟶ I) (ι : I ⟶ F.obj U.X)
    (hπι : π ≫ ι = F.map U.p) (hιπ : ι ≫ π = 𝟙 I) :
    ((functorExtension C D).obj F).obj U ≅ I :=
  (toKaroubiEquivalence D).inverse.mapIso
    (splitKaroubiIso (F.map U.p) (by rw [← F.map_comp, U.idem]) π ι hπι hιπ) ≪≫
    (toKaroubiEquivalence D).unitIso.symm.app I

end General

variable {k : Type u} [Field k] {d t : ℕ} {P : Relations k d t}
variable {Y : Type v} [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y]
variable (X : Representation P Y)

instance derivedEmbeddingAdditive : (derivedEmbedding.{u,max u v} k).Additive :=
  inferInstanceAs ((inclusion k ⋙ DerivedCategory.Qh).Additive)

instance derivedToEssImageAdditive : ((derivedEmbedding.{u,max u v} k).toEssImage).Additive := by
  dsimp [Functor.toEssImage]
  infer_instance

instance derivedQuotientEvaluationAdditive : (derivedQuotientEvaluation X).Additive := by
  dsimp [derivedQuotientEvaluation]
  infer_instance

/-- The manuscript's additive extension of evaluation to all of Kar(Q), with
values in the actual bounded finite-dimensional derived category. -/
def completedDerivedEvaluation : Karoubi (BoundedQ P) ⥤ FiniteVectorDerived.{u,v} (k := k) :=
  (functorExtension _ _).obj (derivedQuotientEvaluation X)

instance completedDerivedEvaluationAdditive : (completedDerivedEvaluation X).Additive :=
  completedExtensionAdditive (derivedQuotientEvaluation X)

def completedDerivedEvaluationFactors :
    toKaroubi (BoundedQ P) ⋙ completedDerivedEvaluation X ≅ derivedQuotientEvaluation X :=
  completedExtensionFactors (derivedQuotientEvaluation X)
end LittleFinitistic.QuadraticEncoding

end

end OAI
