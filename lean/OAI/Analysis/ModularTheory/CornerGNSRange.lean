import OAI.Analysis.ModularTheory.CornerGNS
import OAI.Analysis.ModularTheory.CornerVectors
import OAI.Analysis.OperatorAlgebra.GNSCornerRange

namespace OAI

/-! The finite tracial GNS range is exactly the actual two-sided corner. -/
noncomputable section
open MeasureTheory
open scoped Topology ComplexOrder
namespace WeakPureInfiniteness
open BoundedRecovery

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local irreducible] modularCompressedTracialState

lemma modularTracialCornerProjection_lift_vector (S : StandardModularData H) (n : ℕ)
    (a : (modularCompressedCorner S n).toStarSubalgebra) :
    modularTracialCornerProjection S n
      (isometricCornerLift (modularCornerInclusion (H := H) n) a.val
        (modularCoreWeightVector S n)) =
      isometricCornerLift (modularCornerInclusion (H := H) n) a.val
        (modularCoreWeightVector S n) := by
  let L := isometricCornerLift (modularCornerInclusion (H := H) n) a.val
  have hL : L ∈ modularCrossedProduct volume S := modularCornerLift_mem S n a
  have hv := modularFiniteWeightMap_cut S L hL n
  calc
    _ = modularTracialCornerProjection S n
        (modularFiniteWeightMap S (modularFiniteWeightCut S L hL n)) :=
      congrArg (modularTracialCornerProjection S n) hv.symm
    _ = (modularFiniteProjection (H := H) n * (L * modularFiniteProjection (H := H) n) *
        modularFiniteProjection (H := H) n) (modularCoreWeightVector S n) :=
      modularTracialCornerProjection_vector_explicit S n (modularFiniteWeightCut S L hL n)
    _ = _ := by
      change (modularFiniteProjection (H := H) n *
        (isometricCornerLift (modularCornerInclusion (H := H) n) a.val *
          modularFiniteProjection (H := H) n) * modularFiniteProjection (H := H) n)
            (modularCoreWeightVector S n) = _
      rw [modularCornerLift_right, modularCornerLift_left, modularCornerLift_right]

lemma modularCornerGNSInclusion_fixed (S : StandardModularData H) (n : ℕ)
    (x : gnsHilbert (modularCompressedTracialState S n).functional) :
    modularTracialCornerProjection S (n + 1) (modularCornerGNSInclusion S n x) =
      modularCornerGNSInclusion S n x :=
  gnsInclusion_fixed_of_vectors (modularCompressedTracialState S n).functional
    (modularCornerGNSInclusion S n) (modularTracialCornerProjection S (n + 1))
    (((‖modularCoreWeightVector S (n + 1)‖⁻¹ : ℝ) : ℂ))
    (fun a => isometricCornerLift (modularCornerInclusion (H := H) (n + 1)) a.val
      (modularCoreWeightVector S (n + 1)))
    (modularCornerGNSInclusion_vector S n)
    (modularTracialCornerProjection_lift_vector S (n + 1)) x

lemma modularTracialCornerProjection_mem_gnsRange (S : StandardModularData H) (n : ℕ)
    (x : Lp H 2 (volume : Measure ℝ)) :
    modularTracialCornerProjection S (n + 1) x ∈ Set.range (modularCornerGNSInclusion S n) := by
  refine gnsInclusion_range_of_dense_vectors
    (modularCompressedTracialState S n).functional (modularCornerGNSInclusion S n)
    (modularTracialCornerProjection S (n + 1))
    (((‖modularCoreWeightVector S (n + 1)‖⁻¹ : ℝ) : ℂ)) ?_
    (fun a => isometricCornerLift (modularCornerInclusion (H := H) (n + 1)) a.val
      (modularCoreWeightVector S (n + 1)))
    (modularCornerGNSInclusion_vector S n)
    (modularFiniteWeightMap S) (modularFiniteWeightMap_dense S)
    (fun T => modularCoreCompression S (n + 1) T.val T.property.1)
    (modularTracialCornerProjection_vector_compression S (n + 1)) x
  exact_mod_cast inv_ne_zero (norm_ne_zero_iff.mpr (modularCoreWeightVector_succ_ne_zero S n))

lemma modularCornerGNSInclusion_projection (S : StandardModularData H) (n : ℕ) :
    modularTracialCornerProjection S (n + 1) =
      isometricCornerProjection (modularCornerGNSInclusion S n) :=
  isometricCornerProjection_eq_of_range (modularCornerGNSInclusion S n)
    (modularTracialCornerProjection S (n + 1))
    (modularTracialCornerProjection_isStarProjection S (n + 1))
    (modularCornerGNSInclusion_fixed S n) (modularTracialCornerProjection_mem_gnsRange S n)

end WeakPureInfiniteness

end

end OAI
