import OAI.Analysis.KadisonSimilarity.Tracial.TracialEmbeddingTransport
import OAI.Analysis.KadisonSimilarity.Tracial.TracialUltrapowerConstants
import OAI.Analysis.KadisonSimilarity.Tracial.TracialSubalgebraTransfer

namespace OAI

/-! Exact recovery of a commutator through trace-preserving embeddings.
This is the final direction of the ultrapower transfer: a bound on the
constant subalgebra's compressed commutator bounds the original operator. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  (τA : A →ₚ[ℂ] ℂ) (τB : B →ₚ[ℂ] ℂ)
  (trB : ∀ a b : B, τB (a * b) = τB (b * a))
  (φ : A →⋆ₐ[ℂ] B) (hφ : ∀ a, τB (φ a) = τA a)

local notation "G" => gnsTracialGeometry τB trB
local notation "V" => TracialCornerGeometry.baseInclusion (gnsTracialGeometry τB trB) φ.range

include hφ in
omit [StarOrderedRing A] in
theorem gnsGeometry_preserves_trace :
    ∀ a, (G).trace (φ a) = τA a := hφ

local notation "U" => tracialRangeIsometry τA (gnsTracialGeometry τB trB) φ
  (gnsGeometry_preserves_trace τA τB trB φ hφ)
local notation "J" => gnsTracialHomIsometry τA τB φ hφ

/-- Factoring the GNS embedding through the completed range is exact. -/
theorem tracialRangeIsometry_inclusion :
    (V).toContinuousLinearMap.comp (U).toContinuousLinearMap = (J).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro ξ
  refine (gnsTracialVector_dense τA).induction_on ξ
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  change V (U (gnsTracialVector τA a)) = J (gnsTracialVector τA a)
  rw [tracialRangeIsometry_vector, gnsTracialHomIsometry_vector]
  rfl

/-- The range-space isometry intertwines the actual left representations. -/
theorem tracialRangeIsometry_left (a : A) :
    ((G).baseRepresentation φ.range (φ.rangeRestrict a)).comp (U).toContinuousLinearMap =
      (U).toContinuousLinearMap.comp (τA.gnsStarAlgHom a) := by
  apply ContinuousLinearMap.ext
  intro ξ
  refine (gnsTracialVector_dense τA).induction_on ξ
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b
  change (G).baseRepresentation φ.range (φ.rangeRestrict a) (U (gnsTracialVector τA b)) =
    U (τA.gnsStarAlgHom a (gnsTracialVector τA b))
  rw [gnsTracialVector_left, tracialRangeIsometry_vector, tracialRangeIsometry_vector]
  apply Subtype.ext
  change (G).left (φ a) ((G).vector (φ b)) = (G).vector (φ (a * b))
  rw [(G).left_vector, map_mul φ a b]

/-- No norm is lost when using a bound on the compressed constant algebra
to recover the original commutator. Only compression equality is needed. -/
theorem norm_commutator_le_tracial_range_compression
    (T : τA.GNS →L[ℂ] τA.GNS) (S : τB.GNS →L[ℂ] τB.GNS)
    (hT : (J).toContinuousLinearMap.adjoint.comp (S.comp (J).toContinuousLinearMap) = T)
    (a : A) :
    ‖commutator T (τA.gnsStarAlgHom a)‖ ≤
      ‖(G).baseOperator φ.range (commutator S (τB.gnsStarAlgHom (φ a)))‖ := by
  have hc : (U).toContinuousLinearMap.adjoint.comp
      (((G).baseOperator φ.range S).comp (U).toContinuousLinearMap) = T := by
    change (U).toContinuousLinearMap.adjoint.comp
      (((V).toContinuousLinearMap.adjoint.comp (S.comp (V).toContinuousLinearMap)).comp
        (U).toContinuousLinearMap) = T
    rw [compression_through_composite, tracialRangeIsometry_inclusion τA τB trB φ hφ, hT]
  have hb := norm_reducing_compression_commutator_le U ((G).baseOperator φ.range S)
    ((G).baseRepresentation φ.range (φ.rangeRestrict a)) (τA.gnsStarAlgHom a)
    (tracialRangeIsometry_left τA τB trB φ hφ a) (by
      simpa only [map_star, ContinuousLinearMap.star_eq_adjoint] using
        tracialRangeIsometry_left τA τB trB φ hφ (star a))
    (le_refl ‖commutator ((G).baseOperator φ.range S)
      ((G).baseRepresentation φ.range (φ.rangeRestrict a))‖)
  rw [hc] at hb
  rwa [← (G).baseOperator_commutator_subalgebra φ.range S (φ.rangeRestrict a)] at hb

section Composition
variable {C : Type*} [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
  (τC : C →ₚ[ℂ] ℂ) (ψ : B →⋆ₐ[ℂ] C) (hψ : ∀ b, τC (ψ b) = τB b)

/-- GNS embeddings compose on the completed Hilbert spaces. -/
theorem gnsTracialHomIsometry_comp :
    (gnsTracialHomIsometry τB τC ψ hψ).toContinuousLinearMap.comp
      (gnsTracialHomIsometry τA τB φ hφ).toContinuousLinearMap =
    (gnsTracialHomIsometry τA τC (ψ.comp φ)
      (fun a => (hψ (φ a)).trans (hφ a))).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro ξ
  refine (gnsTracialVector_dense τA).induction_on ξ
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  change gnsTracialHomIsometry τB τC ψ hψ
    (gnsTracialHomIsometry τA τB φ hφ (gnsTracialVector τA a)) =
      gnsTracialHomIsometry τA τC (ψ.comp φ)
        (fun a => (hψ (φ a)).trans (hφ a)) (gnsTracialVector τA a)
  calc
    _ = gnsTracialVector τC (ψ (φ a)) := by
      rw [gnsTracialHomIsometry_vector, gnsTracialHomIsometry_vector]
    _ = _ := (gnsTracialHomIsometry_vector τA τC (ψ.comp φ) _ a).symm

end Composition
end KadisonSimilarity

end

end OAI
