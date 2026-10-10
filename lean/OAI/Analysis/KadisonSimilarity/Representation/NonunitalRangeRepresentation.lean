import OAI.Analysis.KadisonSimilarity.Representation.ProjectionFieldReduction

namespace OAI

/-! A nonunital representation of a unital C-star algebra becomes unital
on the range of the image of its unit. This also covers the zero fibers
used outside a conull spectral base. -/

noncomputable section
namespace KadisonSimilarity

variable {B K : Type*} [CStarAlgebra B]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def nonunitalUnitProjection (ρ : B →⋆ₙₐ[ℂ] (K →L[ℂ] K)) : K →L[ℂ] K := ρ 1

theorem nonunitalUnitProjection_isStarProjection (ρ : B →⋆ₙₐ[ℂ] (K →L[ℂ] K)) :
    IsStarProjection (nonunitalUnitProjection ρ) :=
  (IsStarProjection.one B).map ρ

theorem nonunitalUnitProjection_commutes (ρ : B →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (b : B) :
    Commute (nonunitalUnitProjection ρ) (ρ b) := by
  change ρ 1 * ρ b = ρ b * ρ 1
  rw [← map_mul, ← map_mul, one_mul, mul_one]

def nonunitalRangeRepresentation (ρ : B →⋆ₙₐ[ℂ] (K →L[ℂ] K)) :
    B →⋆ₐ[ℂ]
      (projectionFiber (nonunitalUnitProjection ρ) (nonunitalUnitProjection_isStarProjection ρ) →L[ℂ]
        projectionFiber (nonunitalUnitProjection ρ) (nonunitalUnitProjection_isStarProjection ρ)) where
  toFun b := projectionFiberAction (nonunitalUnitProjection ρ)
    (nonunitalUnitProjection_isStarProjection ρ) (ρ b) (nonunitalUnitProjection_commutes ρ b)
  map_zero' := by ext x; simp
  map_one' := by
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    exact projectionFiber_fixed _ _ x
  map_add' a b := by ext x; simp
  map_mul' a b := by ext x; simp [mul_apply_eq_comp]
  commutes' c := by
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    change ρ (algebraMap ℂ B c) (x : K) = c • (x : K)
    rw [Algebra.algebraMap_eq_smul_one, map_smul]
    change c • (nonunitalUnitProjection ρ (x : K)) = c • (x : K)
    rw [projectionFiber_fixed]
  map_star' a := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    change inner ℂ (y : K) (ρ (star a) (x : K)) =
      inner ℂ y ((projectionFiberAction _ _ (ρ a) _).adjoint x)
    rw [ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ (y : K) (ρ (star a) (x : K)) = inner ℂ (ρ a (y : K)) (x : K)
    rw [map_star]
    exact ContinuousLinearMap.adjoint_inner_right _ _ _

@[simp] theorem nonunitalRangeRepresentation_coe
    (ρ : B →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (b : B)
    (x : projectionFiber (nonunitalUnitProjection ρ) (nonunitalUnitProjection_isStarProjection ρ)) :
    (nonunitalRangeRepresentation ρ b x : K) = ρ b (x : K) := rfl

end KadisonSimilarity

end

end OAI
