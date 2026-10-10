import OAI.Analysis.KadisonSimilarity.Representation.ProjectionFieldReduction

namespace OAI

/-! Algebraic identities for compressing supported operators to the actual
range of an orthogonal projection. -/

noncomputable section
namespace KadisonSimilarity

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (p : H →L[ℂ] H) (hp : IsStarProjection p)

theorem projectionFiberCompression_sub (T U : H →L[ℂ] H) :
    projectionFiberCompression p hp (T - U) =
      projectionFiberCompression p hp T - projectionFiberCompression p hp U := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  change p ((T - U) (x : H)) = p (T (x : H)) - p (U (x : H))
  simp only [sub_apply, map_sub]

theorem projectionFiberCompression_mul (T U : H →L[ℂ] H) (hU : p * U = U) :
    projectionFiberCompression p hp (T * U) =
      projectionFiberCompression p hp T * projectionFiberCompression p hp U := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  change p (T (U (x : H))) = p (T (p (U (x : H))))
  have h := congrArg (fun R : H →L[ℂ] H => R (x : H)) hU
  change p (U (x : H)) = U (x : H) at h
  rw [h]

end KadisonSimilarity

end

end OAI
