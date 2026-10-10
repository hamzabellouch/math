import OAI.Analysis.ModularTheory.TracialCorners
import OAI.Analysis.ModularTheory.CornerRepresentation

namespace OAI

/-! Concrete vectors in the two-sided finite tracial corners. -/
noncomputable section
open MeasureTheory
namespace WeakPureInfiniteness
open BoundedRecovery

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def modularCoreCompression (S : StandardModularData H) (n : ℕ)
    (a : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (ha : a ∈ modularCrossedProduct volume S) :
    (modularCompressedCorner S n).toStarSubalgebra := by
  refine ⟨isometricCornerCompress (modularCornerInclusion (H := H) n) a, ?_⟩
  apply (isometricCornerVonNeumann_mem_iff (modularCrossedProduct volume S)
    (modularCornerInclusion (H := H) n) (modularCornerProjection_mem S n) _).mpr
  rw [isometricCornerLift_compress, modularCornerInclusion_projection]
  exact mul_mem (mul_mem (modularFiniteProjection_mem S n) ha)
    (modularFiniteProjection_mem S n)

lemma modularCoreCompression_lift (S : StandardModularData H) (n : ℕ)
    (a : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (ha : a ∈ modularCrossedProduct volume S) :
    isometricCornerLift (modularCornerInclusion (H := H) n)
      (modularCoreCompression S n a ha).val =
        modularFiniteProjection (H := H) n * a * modularFiniteProjection (H := H) n := by
  change isometricCornerLift (modularCornerInclusion (H := H) n)
    (isometricCornerCompress (modularCornerInclusion (H := H) n) a) = _
  rw [isometricCornerLift_compress, modularCornerInclusion_projection]

lemma modularFiniteWeight_supported_vector (S : StandardModularData H) (n : ℕ)
    (T : modularFiniteWeightSpace S)
    (hT : T.val * modularFiniteProjection (H := H) n = T.val) :
    modularFiniteWeightMap S T = T.val (modularCoreWeightVector S n) := by
  have he : modularFiniteWeightCut S T.val T.property.1 n = T := by
    apply Subtype.ext
    exact hT
  have h := modularFiniteWeightMap_cut S T.val T.property.1 n
  rwa [he] at h

lemma modularFiniteWeightCorner_supported (S : StandardModularData H) (n : ℕ)
    (T : modularFiniteWeightSpace S) :
    (modularFiniteWeightCorner S n T).val * modularFiniteProjection (H := H) n =
      (modularFiniteWeightCorner S n T).val := by
  let p := modularFiniteProjection (H := H) n
  have hp : p * p = p := (modularFiniteProjection_isStarProjection n).isIdempotentElem
  change (p * (T.val * p)) * p = p * (T.val * p)
  calc
    _ = p * (T.val * (p * p)) := by noncomm_ring
    _ = _ := by rw [hp]

lemma modularTracialCornerProjection_vector_explicit (S : StandardModularData H) (n : ℕ)
    (T : modularFiniteWeightSpace S) :
    modularTracialCornerProjection S n (modularFiniteWeightMap S T) =
      (modularFiniteProjection (H := H) n * T.val * modularFiniteProjection (H := H) n)
        (modularCoreWeightVector S n) := by
  rw [modularTracialCornerProjection_vector,
    modularFiniteWeight_supported_vector S n _ (modularFiniteWeightCorner_supported S n T)]
  rfl

lemma modularTracialCornerProjection_vector_compression (S : StandardModularData H) (n : ℕ)
    (T : modularFiniteWeightSpace S) :
    modularTracialCornerProjection S n (modularFiniteWeightMap S T) =
      isometricCornerLift (modularCornerInclusion (H := H) n)
        (modularCoreCompression S n T.val T.property.1).val (modularCoreWeightVector S n) := by
  rw [modularCoreCompression_lift, modularTracialCornerProjection_vector_explicit]

end WeakPureInfiniteness

end

end OAI
