import OAI.Analysis.OperatorAlgebra.IntertwinerCompression
import OAI.Analysis.OperatorAlgebra.StandardCommutantOpposite
import OAI.Analysis.Nuclearity.CPFaithfulRestriction
import OAI.Analysis.ModularTheory.CommutantExpectation

namespace OAI

/-! Compress a commuting representation through the constructed intertwiner.
The result is an actual CP map into the standard commutant. -/
noncomputable section
open scoped ComplexOrder
namespace WeakPureInfiniteness
open BoundedRecovery KirchbergRordam.GenericRW.GroupedFactors

variable {A B H K : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [PartialOrder B] [StarOrderedRing B] in
lemma intertwiner_compression_mem (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (V : K →L[ℂ] H)
    (hV : ∀ a, V.comp (ρ a) = (π a).comp V)
    (η : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (hc : ∀ a b, Commute (π a) (η b))
    (S : StandardModularData K) (hS : S.M = bicommutant ρ.range) (b : B) :
    hilbertCompression η.toNonUnitalStarAlgHom V b ∈ S.M.commutant := by
  rw [hS, representation_bicommutant_commutant]
  apply mem_representationCommutant ρ
  intro a
  exact (intertwiner_compression_commutes ρ π V hV (η b) (fun a => hc a b) a).symm

def intertwinerCommutantCP (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (V : K →L[ℂ] H)
    (hV : ∀ a, V.comp (ρ a) = (π a).comp V)
    (η : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (hc : ∀ a b, Commute (π a) (η b))
    (S : StandardModularData K) (hS : S.M = bicommutant ρ.range) :
    B →L[ℂ] S.M.commutant.toStarSubalgebra :=
  (hilbertCompression η.toNonUnitalStarAlgHom V).codRestrict
    S.M.commutant.toStarSubalgebra.toSubalgebra.toSubmodule
    (intertwiner_compression_mem ρ π V hV η hc S hS)

lemma intertwinerCommutantCP_cp (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (V : K →L[ℂ] H)
    (hV : ∀ a, V.comp (ρ a) = (π a).comp V)
    (η : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (hc : ∀ a b, Commute (π a) (η b))
    (S : StandardModularData K) (hS : S.M = bicommutant ρ.range) :
    CompletelyPositive (intertwinerCommutantCP ρ π V hV η hc S hS) := by
  apply completelyPositive_of_faithful_postcomp _
    S.M.commutant.toStarSubalgebra.subtype.toNonUnitalStarAlgHom Subtype.val_injective
  exact hilbertCompression_cp η.toNonUnitalStarAlgHom V

omit [PartialOrder B] [StarOrderedRing B] in
lemma intertwinerCommutantCP_norm_le (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (V : K →L[ℂ] H)
    (hV : ∀ a, V.comp (ρ a) = (π a).comp V)
    (η : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (hc : ∀ a b, Commute (π a) (η b))
    (S : StandardModularData K) (hS : S.M = bicommutant ρ.range) :
    ‖intertwinerCommutantCP ρ π V hV η hc S hS‖ ≤ ‖V‖ * ‖V‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro b
  exact hilbertCompressionLinear_bound η.toNonUnitalStarAlgHom V b

end WeakPureInfiniteness

end

end OAI
