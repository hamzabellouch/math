import OAI.Analysis.KadisonSimilarity.Derivation.CyclicSpectralIsometry
import OAI.Analysis.KadisonSimilarity.Representation.SpectralBaseTopology

namespace OAI

/-! Scalar spectral coordinates for one cyclic subspace of a commutative
representation. These are the components of the central Hilbert model. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

variable {A H : Type*} [CommCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance spectralMeasurableSpace : MeasurableSpace (WeakDual.characterSpace ℂ A) :=
  borel (WeakDual.characterSpace ℂ A)
local instance spectralBorelSpace : BorelSpace (WeakDual.characterSpace ℂ A) := ⟨rfl⟩

def commutativeSpectralCalculus (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    C(WeakDual.characterSpace ℂ A, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  π.comp (gelfandStarTransform A).symm.toStarAlgHom

def commutativeVectorMeasure (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    Measure (WeakDual.characterSpace ℂ A) :=
  VectorSpectralMeasure.measure (commutativeSpectralCalculus π) ξ

instance commutativeVectorMeasure_finite (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    IsFiniteMeasure (commutativeVectorMeasure π ξ) :=
  inferInstanceAs (IsFiniteMeasure (VectorSpectralMeasure.measure (commutativeSpectralCalculus π) ξ))

instance commutativeVectorMeasure_regular (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    (commutativeVectorMeasure π ξ).Regular :=
  inferInstanceAs ((VectorSpectralMeasure.measure (commutativeSpectralCalculus π) ξ).Regular)

def commutativeCyclicIsometry (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    Lp ℂ 2 (commutativeVectorMeasure π ξ) →ₗᵢ[ℂ] H :=
  VectorSpectralMeasure.cyclicIsometry (commutativeSpectralCalculus π) ξ

theorem commutativeCyclicIsometry_gelfand
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (a : A) :
    commutativeCyclicIsometry π ξ
      (ContinuousMap.toLp 2 (commutativeVectorMeasure π ξ) ℂ (gelfandStarTransform A a)) = π a ξ := by
  change VectorSpectralMeasure.cyclicMap (commutativeSpectralCalculus π) ξ
    (ContinuousMap.toLp 2 (VectorSpectralMeasure.measure (commutativeSpectralCalculus π) ξ) ℂ
      (gelfandStarTransform A a)) = _
  rw [VectorSpectralMeasure.cyclicMap_toLp]
  change π ((gelfandStarTransform A).symm (gelfandStarTransform A a)) ξ = _
  rw [StarAlgEquiv.symm_apply_apply]

theorem commutativeCyclicIsometry_range
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    Set.range (commutativeCyclicIsometry π ξ) = closure (Set.range (fun a : A => π a ξ)) := by
  change Set.range (VectorSpectralMeasure.cyclicMap (commutativeSpectralCalculus π) ξ) = _
  rw [VectorSpectralMeasure.cyclicMap_range]
  congr 1
  apply Set.Subset.antisymm
  · rintro _ ⟨f, rfl⟩
    exact ⟨(gelfandStarTransform A).symm f, rfl⟩
  · rintro _ ⟨a, rfl⟩
    refine ⟨gelfandStarTransform A a, ?_⟩
    change π ((gelfandStarTransform A).symm (gelfandStarTransform A a)) ξ = π a ξ
    rw [StarAlgEquiv.symm_apply_apply]

end KadisonSimilarity

end

end OAI
