import OAI.Analysis.OperatorAlgebra.IntertwinerCommutantCP
import OAI.Analysis.Nuclearity.MinimalRightCPMap

namespace OAI

/-! Tensoring the actual commuting compression with the standard left action.
The bound is uniform in the finite tensor being tested. -/
noncomputable section
open scoped ComplexOrder TensorProduct
namespace WeakPureInfiniteness
open BoundedRecovery KirchbergRordam.GenericRW.GroupedFactors

variable {A B H K : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def standardLeftFactor (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (S : StandardModularData K) (hS : S.M = bicommutant ρ.range) :
    A →⋆ₐ[ℂ] S.M.toStarSubalgebra where
  toFun a := ⟨ρ a, hS ▸ subset_bicommutant ρ.range (ρ a) ⟨a, rfl⟩⟩
  map_zero' := Subtype.ext (map_zero ρ)
  map_one' := Subtype.ext (map_one ρ)
  map_add' a b := Subtype.ext (map_add ρ a b)
  map_mul' a b := Subtype.ext (map_mul ρ a b)
  commutes' c := Subtype.ext (ρ.commutes c)
  map_star' a := Subtype.ext (map_star ρ a)

def intertwinerOppositeCP (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (V : K →L[ℂ] H)
    (hV : ∀ a, V.comp (ρ a) = (π a).comp V)
    (η : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (hc : ∀ a b, Commute (π a) (η b))
    (S : StandardModularData K) (hS : S.M = bicommutant ρ.range) :
    B →L[ℂ] S.M.toStarSubalgebraᵐᵒᵖ :=
  (starHomContinuousLinear (standardCommutantEquiv S).symm.toNonUnitalStarAlgHom).comp
    (intertwinerCommutantCP ρ π V hV η hc S hS)

lemma intertwinerOppositeCP_cp (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (V : K →L[ℂ] H)
    (hV : ∀ a, V.comp (ρ a) = (π a).comp V)
    (η : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (hc : ∀ a b, Commute (π a) (η b))
    (S : StandardModularData K) (hS : S.M = bicommutant ρ.range) :
    CompletelyPositive (intertwinerOppositeCP ρ π V hV η hc S hS) :=
  completelyPositive_comp _ _ (intertwinerCommutantCP_cp ρ π V hV η hc S hS)
    (starHomContinuous_completelyPositive _)

omit [PartialOrder B] [StarOrderedRing B] in
lemma intertwinerOppositeCP_norm_le (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (V : K →L[ℂ] H)
    (hV : ∀ a, V.comp (ρ a) = (π a).comp V)
    (η : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (hc : ∀ a b, Commute (π a) (η b))
    (S : StandardModularData K) (hS : S.M = bicommutant ρ.range) :
    ‖intertwinerOppositeCP ρ π V hV η hc S hS‖ ≤ ‖V‖ * ‖V‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro b
  exact (NonUnitalStarAlgHom.norm_apply_le
    (standardCommutantEquiv S).symm.toNonUnitalStarAlgHom _).trans
      (hilbertCompressionLinear_bound η.toNonUnitalStarAlgHom V b)

omit [PartialOrder B] [StarOrderedRing B] in
lemma intertwinerOppositeCP_evaluate (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (V : K →L[ℂ] H)
    (hV : ∀ a, V.comp (ρ a) = (π a).comp V)
    (η : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (hc : ∀ a b, Commute (π a) (η b))
    (S : StandardModularData K) (hS : S.M = bicommutant ρ.range) (b : B) :
    ((standardCommutantEquiv S) (intertwinerOppositeCP ρ π V hV η hc S hS b)).val =
      V.adjoint.comp ((η b).comp V) := by
  change ((standardCommutantEquiv S) ((standardCommutantEquiv S).symm
    (intertwinerCommutantCP ρ π V hV η hc S hS b))).val = _
  rw [StarAlgEquiv.apply_symm_apply]
  rfl

end WeakPureInfiniteness

end

end OAI
