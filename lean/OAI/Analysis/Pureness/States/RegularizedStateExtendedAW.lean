import OAI.Analysis.Pureness.States.RegularizedStateSpatialTransport
import OAI.Analysis.Pureness.States.QuotientAWStar
import OAI.Analysis.Pureness.Projections.QuotientProjectionNormality
import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientFinite

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace OrderedSemigroup
open scoped TensorProduct NNReal ENNReal
universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (hsimple : TopologicallySimple A) (y : finiteCuntzSubmonoid (A := A))
variable (hy : y ≠ 0) (f : StateSpace y)

abbrev regularizedStateExtendedQuasitrace : ComplexQuasitrace (RegularizedStateExtendedAW hsimple y hy f) :=
  (matrixStateAWPositive hsimple y hy f freeGroupScalarUltrafilter).quotientComplexQuasitrace
    (matrixStateAWPositive_triangle hsimple y hy f freeGroupScalarUltrafilter)
    (matrixStateAWPositive_sqrt hsimple y hy f freeGroupScalarUltrafilter)

lemma regularizedStateExtendedQuasitrace_unit :
    regularizedStateExtendedQuasitrace hsimple y hy f 1 = 1 := by
  rw [PositiveQuasitrace.quotientComplexQuasitrace_eq]
  have h := (matrixStateAWPositive hsimple y hy f freeGroupScalarUltrafilter).quotientValue_embedding
    (matrixStateAWPositive_triangle hsimple y hy f freeGroupScalarUltrafilter)
    (matrixStateAWPositive_sqrt hsimple y hy f freeGroupScalarUltrafilter) 1
  let U := matrixStateAWPositive hsimple y hy f freeGroupScalarUltrafilter
  let hu := matrixStateAWPositive_triangle hsimple y hy f freeGroupScalarUltrafilter
  let hs := matrixStateAWPositive_sqrt hsimple y hy f freeGroupScalarUltrafilter
  have he : U.quotientEmbedding hu 1 = 1 := (U.quotientEmbedding hu).map_one
  exact ((congrArg (U.quotientValue hu hs) he).symm.trans h).trans
    ((matrixStateAWPositive_complex hsimple y hy f freeGroupScalarUltrafilter 1).trans
      (ultralimitAWQuasitrace_unit
        (normalizedMatrixStatePositiveQuasitrace hsimple y hy f) freeGroupScalarUltrafilter
        (normalizedMatrixStatePositiveQuasitrace_unit hsimple y hy f)
        (normalizedMatrixStatePositiveQuasitrace_metricSize_add hsimple y hy f)
        (normalizedMatrixStatePositiveQuasitrace_sqrt_add hsimple y hy f)))

lemma regularizedStateExtendedQuasitrace_faithful (x : RegularizedStateExtendedAW hsimple y hy f) :
    regularizedStateExtendedQuasitrace hsimple y hy f (star x*x) = 0 ↔ x = 0 := by
  rw [PositiveQuasitrace.quotientComplexQuasitrace_eq]
  exact PositiveQuasitrace.quotientValue_square_eq_zero_iff _ _ _ x

lemma regularizedStateExtendedAW_finite (x : RegularizedStateExtendedAW hsimple y hy f)
    (hx : star x*x = 1) : x*star x = 1 :=
  PositiveQuasitrace.cauchyQuotient_isometry_unitary _ _
    (matrixStateAWPositive_sqrt hsimple y hy f freeGroupScalarUltrafilter) x hx

lemma regularizedStateExtendedAW_annihilator (S : Set (RegularizedStateExtendedAW hsimple y hy f)) :
    ∃ p, IsStarProjection p ∧ ∀ z, (∀ a ∈ S, a*z=0) ↔ p*z=z :=
  PositiveQuasitrace.quotient_right_annihilator_projection _ _
    (matrixStateAWPositive_sqrt hsimple y hy f freeGroupScalarUltrafilter) S

lemma regularizedStateExtendedQuasitrace_normal
    (S : Set (RegularizedStateExtendedAW hsimple y hy f)) (hne : S.Nonempty)
    (hp : ∀ p ∈ S, IsStarProjection p) (hd : DirectedOn (· ≤ ·) S) :
    ∃ p, IsStarProjection p ∧ (∀ q ∈ S, q ≤ p) ∧
      (∀ q, IsStarProjection q → (∀ a ∈ S, a ≤ q) → p ≤ q) ∧
      (regularizedStateExtendedQuasitrace hsimple y hy f p).re =
        sSup ((fun q => (regularizedStateExtendedQuasitrace hsimple y hy f q).re) '' S) := by
  simpa only [PositiveQuasitrace.quotientComplexQuasitrace_eq] using
    (matrixStateAWPositive hsimple y hy f freeGroupScalarUltrafilter).exists_quotient_directed_projection_sup
      (matrixStateAWPositive_triangle hsimple y hy f freeGroupScalarUltrafilter)
      (matrixStateAWPositive_sqrt hsimple y hy f freeGroupScalarUltrafilter) S hne hp hd

variable (hA : IsNuclear.{u,0} A)

lemma regularizedStateSpatialExtension_left_value
    (x : RegularizedStateCauchyQuotient hsimple y hy f 0) :
    regularizedStateExtendedQuasitrace hsimple y hy f
      (regularizedStateSpatialExtension hsimple y hy f hA
        (spatialCompletionMap
          ((regularizedStateCauchyPositive hsimple y hy f).cauchyTargetGNS
            (regularizedStateCauchyTriangle hsimple y hy f))
          (reducedGroupAlgebra (FreeGroup ℕ)).subtype (x ⊗ₜ[ℂ] 1))) =
        normalizedStateCauchyValue hsimple y hy f x := by
  rw [PositiveQuasitrace.quotientComplexQuasitrace_eq]
  have h := (regularizedStateCauchyPositive hsimple y hy f).cauchySpatialExtension_left_value
    (matrixStateAWPositive hsimple y hy f freeGroupScalarUltrafilter)
    (regularizedStateCauchyTriangle hsimple y hy f)
    (matrixStateAWPositive_triangle hsimple y hy f freeGroupScalarUltrafilter)
    ((regularizedStateCauchyPositive hsimple y hy f).cauchySourceGNS
      (regularizedStateCauchyTriangle hsimple y hy f))
    (finOneOriginalGNS (A := A))
    ((regularizedStateCauchyPositive hsimple y hy f).cauchySourceGNS_injective
      (regularizedStateCauchyTriangle hsimple y hy f))
    (finOneOriginalSpatialAW hsimple y hy f hA)
    (matrixStateFinOneAW hsimple y hy f freeGroupScalarUltrafilter)
    (reducedFreeGroupAWEmbedding hsimple y hy f)
    (finOneOriginalSpatialAW_tensor hsimple y hy f hA)
    (regularizedStateNormalization y f)
    (matrixStateFinOneAW_positive hsimple y hy f freeGroupScalarUltrafilter)
    ((regularizedStateCauchyPositive hsimple y hy f).cauchyTargetGNS
      (regularizedStateCauchyTriangle hsimple y hy f))
    ((regularizedStateCauchyPositive hsimple y hy f).cauchyTargetGNS_injective
      (regularizedStateCauchyTriangle hsimple y hy f))
    (finiteSpectralPositiveQuasitrace_sqrt_add _ _ _ _ 1)
    (matrixStateAWPositive_sqrt hsimple y hy f freeGroupScalarUltrafilter) x
  exact h.trans (congrArg₂ (·*·) (Complex.ofReal_inv _) rfl)

lemma regularizedStateSpatialExtension_right_value (b : ReducedFreeGroup) :
    regularizedStateExtendedQuasitrace hsimple y hy f
      (regularizedStateSpatialExtension hsimple y hy f hA
        (spatialCompletionMap
          ((regularizedStateCauchyPositive hsimple y hy f).cauchyTargetGNS
            (regularizedStateCauchyTriangle hsimple y hy f))
          (reducedGroupAlgebra (FreeGroup ℕ)).subtype (1 ⊗ₜ[ℂ] b))) =
        (reducedGroupTracialState (FreeGroup ℕ)).functional b := by
  rw [PositiveQuasitrace.quotientComplexQuasitrace_eq]
  have h := (regularizedStateCauchyPositive hsimple y hy f).cauchySpatialExtension_right_value
    (matrixStateAWPositive hsimple y hy f freeGroupScalarUltrafilter)
    (regularizedStateCauchyTriangle hsimple y hy f)
    (matrixStateAWPositive_triangle hsimple y hy f freeGroupScalarUltrafilter)
    ((regularizedStateCauchyPositive hsimple y hy f).cauchySourceGNS
      (regularizedStateCauchyTriangle hsimple y hy f))
    (finOneOriginalGNS (A := A))
    ((regularizedStateCauchyPositive hsimple y hy f).cauchySourceGNS_injective
      (regularizedStateCauchyTriangle hsimple y hy f))
    (finOneOriginalSpatialAW hsimple y hy f hA)
    (matrixStateFinOneAW hsimple y hy f freeGroupScalarUltrafilter)
    (reducedFreeGroupAWEmbedding hsimple y hy f)
    (finOneOriginalSpatialAW_tensor hsimple y hy f hA)
    (regularizedStateNormalization y f)
    (matrixStateFinOneAW_positive hsimple y hy f freeGroupScalarUltrafilter)
    ((regularizedStateCauchyPositive hsimple y hy f).cauchyTargetGNS
      (regularizedStateCauchyTriangle hsimple y hy f))
    ((regularizedStateCauchyPositive hsimple y hy f).cauchyTargetGNS_injective
      (regularizedStateCauchyTriangle hsimple y hy f))
    (matrixStateAWPositive_sqrt hsimple y hy f freeGroupScalarUltrafilter) b
  exact h.trans ((matrixStateAWPositive_complex hsimple y hy f freeGroupScalarUltrafilter
    (reducedFreeGroupAWEmbedding hsimple y hy f b)).trans
      (reducedFreeGroupAWEmbedding_value hsimple y hy f b))
end CuntzPureness

end

end OAI
