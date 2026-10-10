import OAI.Analysis.KadisonSimilarity.Representation.RankOneFactorCriterion
import OAI.Analysis.KadisonSimilarity.Representation.BoundedMeasurableField

namespace OAI

/-! Supported rank-one fields supply countably many tests for the full
operator algebra on each projection range. Their bounds and measurability
follow from the projection columns themselves. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A rank-one operator with both vectors in a projection range is supported
on that range on both sides. -/
theorem projection_rankOne_support (p : H →L[ℂ] H) (hp : IsStarProjection p)
    (v w : H) :
    p * InnerProductSpace.rankOne ℂ (p v) (p w) =
        InnerProductSpace.rankOne ℂ (p v) (p w) ∧
      InnerProductSpace.rankOne ℂ (p v) (p w) * p =
        InnerProductSpace.rankOne ℂ (p v) (p w) := by
  have hpp (x : H) : p (p x) = p x :=
    congrArg (fun L : H →L[ℂ] H => L x) hp.isIdempotentElem.eq
  constructor
  · apply ContinuousLinearMap.ext
    intro x
    change p (inner ℂ (p w) x • p v) = inner ℂ (p w) x • p v
    rw [map_smul, hpp]
  · apply ContinuousLinearMap.ext
    intro x
    change inner ℂ (p w) (p x) • p v = inner ℂ (p w) x • p v
    have ha : p.adjoint (p w) = p w := by
      rw [← ContinuousLinearMap.star_eq_adjoint, hp.isSelfAdjoint.star_eq, hpp]
    rw [← ContinuousLinearMap.adjoint_inner_left, ha]

/-- Compression gives the ordinary rank-one operator on the range. -/
theorem projectionFiberCompression_rankOne (p : H →L[ℂ] H) (hp : IsStarProjection p)
    (v w : H) :
    projectionFiberCompression p hp (InnerProductSpace.rankOne ℂ (p v) (p w)) =
      InnerProductSpace.rankOne ℂ (projectionFiberRetraction p hp v)
        (projectionFiberRetraction p hp w) := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  change p (inner ℂ (p w) (x : H) • p v) = inner ℂ (p w) (x : H) • p v
  rw [map_smul]
  exact congrArg (_ • ·) (congrArg (fun L : H →L[ℂ] H => L v) hp.isIdempotentElem.eq)

theorem norm_projection_apply_le (p : H →L[ℂ] H) (hp : IsStarProjection p) (v : H) :
    ‖p v‖ ≤ ‖v‖ := by
  calc
    ‖p v‖ ≤ ‖p‖ * ‖v‖ := p.le_opNorm v
    _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right
      (norm_projection_le_one p hp.isSelfAdjoint.star_eq hp.isIdempotentElem.eq) (norm_nonneg v)
    _ = ‖v‖ := one_mul _

theorem norm_projection_rankOne_le (p : H →L[ℂ] H) (hp : IsStarProjection p)
    (v w : H) : ‖InnerProductSpace.rankOne ℂ (p v) (p w)‖ ≤ ‖v‖ * ‖w‖ := by
  rw [InnerProductSpace.norm_rankOne]
  exact mul_le_mul (norm_projection_apply_le p hp v) (norm_projection_apply_le p hp w)
    (norm_nonneg _) (norm_nonneg _)

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

omit [CompleteSpace H] in
/-- Strongly measurable projection columns give strongly measurable
columns for every supported rank-one field. -/
theorem aestronglyMeasurable_projection_rankOne
    (p : Ω → H →L[ℂ] H)
    (hmeas : ∀ v : H, AEStronglyMeasurable (fun a => p a v) μ) (v w x : H) :
    AEStronglyMeasurable
      (fun a => InnerProductSpace.rankOne ℂ (p a v) (p a w) x) μ := by
  exact ((hmeas w).inner aestronglyMeasurable_const).smul (hmeas v)

end KadisonSimilarity

end

end OAI
