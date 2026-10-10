import OAI.Analysis.KadisonSimilarity.Derivation.CommonCyclicIntertwining
import OAI.Analysis.KadisonSimilarity.Representation.VectorL2Representation
import OAI.Analysis.KadisonSimilarity.Representation.ScalarLocalizationLimit
import OAI.Analysis.KadisonSimilarity.Representation.IntertwinerExtension

namespace OAI

/-! The represented abelian commutant embeds isometrically in the actual
commutant of measurable scalar localizations on a single L² space. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

variable {A H : Type*} [CommCStarAlgebra A] [TopologicalSpace.SeparableSpace A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (D : CyclicDecompositionData π.range)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

def commonScalarRepresentation :
    A →⋆ₐ[ℂ] (CommonCyclicHilbert π D →L[ℂ] CommonCyclicHilbert π D) :=
  (VectorL2.continuousRepresentation (H := ScalarHilbertCoordinates D.generators)
    (cyclicCommonBaseMeasure π D)).comp (gelfandStarTransform A).toStarAlgHom

omit [TopologicalSpace.SeparableSpace A] in
theorem commonScalarRepresentation_apply (a : A) :
    commonScalarRepresentation π D a =
      VectorL2.continuousL2Mul (cyclicCommonBaseMeasure π D) (gelfandStarTransform A a) := rfl

attribute [irreducible] commonScalarRepresentation

omit [TopologicalSpace.SeparableSpace A] in
theorem commonScalarRepresentation_intertwines (a : A) (x : H) :
    cyclicCommonEmbedding π D (π a x) =
      commonScalarRepresentation π D a (cyclicCommonEmbedding π D x) := by
  rw [commonScalarRepresentation_apply]
  exact cyclicCommonEmbedding_intertwines π D a x

omit [TopologicalSpace.SeparableSpace A] in
theorem commonScalarRepresentation_adjoint_intertwines (a : A)
    (y : CommonCyclicHilbert π D) :
    π a ((cyclicCommonEmbedding π D).toContinuousLinearMap.adjoint y) =
      (cyclicCommonEmbedding π D).toContinuousLinearMap.adjoint
        (commonScalarRepresentation π D a y) := by
  have hJs (x : H) : (cyclicCommonEmbedding π D) ((π a).adjoint x) = ((commonScalarRepresentation π D) a).adjoint ((cyclicCommonEmbedding π D) x) := by
    have h := commonScalarRepresentation_intertwines π D (star a) x
    simpa only [map_star, ContinuousLinearMap.star_eq_adjoint] using h
  apply ext_inner_left ℂ
  intro x
  calc
    inner ℂ x (π a ((cyclicCommonEmbedding π D).toContinuousLinearMap.adjoint y)) =
        inner ℂ ((π a).adjoint x) ((cyclicCommonEmbedding π D).toContinuousLinearMap.adjoint y) :=
      (ContinuousLinearMap.adjoint_inner_left (π a) _ _).symm
    _ = inner ℂ ((cyclicCommonEmbedding π D) ((π a).adjoint x)) y :=
      ContinuousLinearMap.adjoint_inner_right (cyclicCommonEmbedding π D).toContinuousLinearMap _ _
    _ = inner ℂ (((commonScalarRepresentation π D) a).adjoint ((cyclicCommonEmbedding π D) x)) y :=
      congrArg (fun z : CommonCyclicHilbert π D => inner ℂ z y) (hJs x)
    _ = inner ℂ ((cyclicCommonEmbedding π D) x) ((commonScalarRepresentation π D) a y) :=
      ContinuousLinearMap.adjoint_inner_left ((commonScalarRepresentation π D) a) _ _
    _ = inner ℂ x ((cyclicCommonEmbedding π D).toContinuousLinearMap.adjoint ((commonScalarRepresentation π D) a y)) :=
      (ContinuousLinearMap.adjoint_inner_right (cyclicCommonEmbedding π D).toContinuousLinearMap _ _).symm

omit [TopologicalSpace.SeparableSpace A] in
theorem commonExtension_commutes_representation
    (T : H →L[ℂ] H) (hT : ∀ a, T * π a = π a * T) (a : A) :
    isometricExtension (cyclicCommonEmbedding π D) T * commonScalarRepresentation π D a =
      commonScalarRepresentation π D a * isometricExtension (cyclicCommonEmbedding π D) T := by
  have hJ (x : H) : (cyclicCommonEmbedding π D) (π a x) = (commonScalarRepresentation π D) a ((cyclicCommonEmbedding π D) x) :=
    commonScalarRepresentation_intertwines π D a x
  have ha := commonScalarRepresentation_adjoint_intertwines π D a
  have hTa (x : H) : T (π a x) = π a (T x) :=
    congrArg (fun L : H →L[ℂ] H => L x) (hT a)
  have he : isometricExtension (cyclicCommonEmbedding π D) T * (commonScalarRepresentation π D) a = (commonScalarRepresentation π D) a * isometricExtension (cyclicCommonEmbedding π D) T := by
    apply ContinuousLinearMap.ext
    intro y
    change (cyclicCommonEmbedding π D) (T ((cyclicCommonEmbedding π D).toContinuousLinearMap.adjoint ((commonScalarRepresentation π D) a y))) =
      (commonScalarRepresentation π D) a ((cyclicCommonEmbedding π D) (T ((cyclicCommonEmbedding π D).toContinuousLinearMap.adjoint y)))
    exact (congrArg (fun z : H => (cyclicCommonEmbedding π D) (T z)) (ha y).symm).trans
      ((congrArg (cyclicCommonEmbedding π D) (hTa ((cyclicCommonEmbedding π D).toContinuousLinearMap.adjoint y))).trans
        (hJ (T ((cyclicCommonEmbedding π D).toContinuousLinearMap.adjoint y))))
  exact he

omit [TopologicalSpace.SeparableSpace A] in
/-- Compression of a scalar-commuting operator lies in the original
represented commutant. -/
theorem commonCompression_commutes_representation
    (Q : CommonCyclicHilbert π D →L[ℂ] CommonCyclicHilbert π D)
    (hQ : ∀ a, Q * commonScalarRepresentation π D a =
      commonScalarRepresentation π D a * Q) (a : A) :
    (((cyclicCommonEmbedding π D).toContinuousLinearMap.adjoint.comp Q).comp
      (cyclicCommonEmbedding π D).toContinuousLinearMap) * π a =
    π a * (((cyclicCommonEmbedding π D).toContinuousLinearMap.adjoint.comp Q).comp
      (cyclicCommonEmbedding π D).toContinuousLinearMap) := by
  apply ContinuousLinearMap.ext
  intro x
  change (cyclicCommonEmbedding π D).toContinuousLinearMap.adjoint
      (Q (cyclicCommonEmbedding π D (π a x))) =
    π a ((cyclicCommonEmbedding π D).toContinuousLinearMap.adjoint
      (Q (cyclicCommonEmbedding π D x)))
  have hq := congrArg (fun L : CommonCyclicHilbert π D →L[ℂ] CommonCyclicHilbert π D =>
    L (cyclicCommonEmbedding π D x)) (hQ a)
  change Q (commonScalarRepresentation π D a (cyclicCommonEmbedding π D x)) =
    commonScalarRepresentation π D a (Q (cyclicCommonEmbedding π D x)) at hq
  rw [commonScalarRepresentation_intertwines, hq,
    ← commonScalarRepresentation_adjoint_intertwines]

omit [TopologicalSpace.SeparableSpace A] in
theorem commonExtension_commutes_continuous
    (T : H →L[ℂ] H) (hT : ∀ a, T * π a = π a * T)
    (f : C(WeakDual.characterSpace ℂ A, ℂ)) :
    isometricExtension (cyclicCommonEmbedding π D) T *
        VectorL2.continuousL2Mul (cyclicCommonBaseMeasure π D) f =
      VectorL2.continuousL2Mul (cyclicCommonBaseMeasure π D) f *
        isometricExtension (cyclicCommonEmbedding π D) T := by
  have h := commonExtension_commutes_representation π D T hT ((gelfandStarTransform A).symm f)
  simpa only [commonScalarRepresentation_apply, StarAlgEquiv.apply_symm_apply] using h

theorem commonExtension_commutes_localizations
    (T : H →L[ℂ] H) (hT : ∀ a, T * π a = π a * T)
    (s : Set (WeakDual.characterSpace ℂ A)) (hs : MeasurableSet s) :
    isometricExtension (cyclicCommonEmbedding π D) T *
        l2Localization (cyclicCommonBaseMeasure π D) s hs =
      l2Localization (cyclicCommonBaseMeasure π D) s hs *
        isometricExtension (cyclicCommonEmbedding π D) T :=
  commutes_localizations_of_continuous (cyclicCommonBaseMeasure π D) _
    (commonExtension_commutes_continuous π D T hT) s hs

end KadisonSimilarity

end

end OAI
