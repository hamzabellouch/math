import OAI.Analysis.KadisonSimilarity.Representation.UnitalizedExtension
import OAI.Analysis.KadisonSimilarity.Representation.ProjectionFieldReduction

namespace OAI

/-! Recover a represented unital algebra from its unitization by restricting
to the image of its old unit. -/

noncomputable section
namespace KadisonSimilarity

variable {B K : Type*} [CStarAlgebra B]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem unitization_old_unit_commutes (b : Unitization ℂ B) :
    Commute (Unitization.inr (1 : B)) b := by
  apply Unitization.ext
  · simp
  · simp [add_comm]

def unitizationProjection (ρ : Unitization ℂ B →⋆ₐ[ℂ] (K →L[ℂ] K)) : K →L[ℂ] K :=
  ρ (Unitization.inr (1 : B))

theorem unitizationProjection_isStarProjection
    (ρ : Unitization ℂ B →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    IsStarProjection (unitizationProjection ρ) := by
  have h : IsStarProjection (Unitization.inr (1 : B) : Unitization ℂ B) := by
    rw [Unitization.isStarProjection_inr_iff]
    exact IsStarProjection.one B
  exact h.map ρ

theorem unitizationProjection_commutes
    (ρ : Unitization ℂ B →⋆ₐ[ℂ] (K →L[ℂ] K)) (b : Unitization ℂ B) :
    Commute (unitizationProjection ρ) (ρ b) :=
  (unitization_old_unit_commutes b).map ρ

/-- The original algebra acts unitally on the range of its own unit, even
though its inclusion into its unitization is nonunital. -/
def unitizationRangeRepresentation (ρ : Unitization ℂ B →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    B →⋆ₐ[ℂ]
      (projectionFiber (unitizationProjection ρ) (unitizationProjection_isStarProjection ρ) →L[ℂ]
        projectionFiber (unitizationProjection ρ) (unitizationProjection_isStarProjection ρ)) where
  toFun b := projectionFiberAction (unitizationProjection ρ)
    (unitizationProjection_isStarProjection ρ) (ρ (Unitization.inr b))
    (unitizationProjection_commutes ρ _)
  map_zero' := by ext x; simp
  map_one' := by
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    exact projectionFiber_fixed _ _ x
  map_add' a b := by ext x; simp
  map_mul' a b := by
    ext x
    simp [Unitization.inr_mul, mul_apply_eq_comp]
  commutes' c := by
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    change ρ (Unitization.inr (algebraMap ℂ B c)) (x : K) = c • (x : K)
    have heq : (Unitization.inr (algebraMap ℂ B c) : Unitization ℂ B) =
        c • Unitization.inr (1 : B) := by
      rw [Algebra.algebraMap_eq_smul_one, Unitization.inr_smul]
    rw [heq, map_smul]
    change c • (unitizationProjection ρ (x : K)) = c • (x : K)
    rw [projectionFiber_fixed]
  map_star' a := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    change inner ℂ (y : K) (ρ (Unitization.inr (star a)) (x : K)) =
      inner ℂ y ((projectionFiberAction _ _ (ρ (Unitization.inr a)) _).adjoint x)
    rw [ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ (y : K) (ρ (Unitization.inr (star a)) (x : K)) =
      inner ℂ (ρ (Unitization.inr a) (y : K)) (x : K)
    rw [Unitization.inr_star, map_star]
    exact ContinuousLinearMap.adjoint_inner_right _ _ _

@[simp] theorem unitizationRangeRepresentation_coe
    (ρ : Unitization ℂ B →⋆ₐ[ℂ] (K →L[ℂ] K)) (b : B)
    (x : projectionFiber (unitizationProjection ρ) (unitizationProjection_isStarProjection ρ)) :
    (unitizationRangeRepresentation ρ b x : K) = ρ (Unitization.inr b) (x : K) := rfl

end KadisonSimilarity

end

end OAI
