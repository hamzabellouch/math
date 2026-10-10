import OAI.Analysis.OperatorAlgebra.IsometricCornerOperators

namespace OAI

/-! The range of an actual orthogonal projection as a complete Hilbert
space, with its isometric inclusion recovering the original projection. -/

noncomputable section
open scoped InnerProductSpace

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def HilbertProjectionRange (p : H →L[ℂ] H) (_hp : IsStarProjection p) := p.range

instance hilbertProjectionRangeNorm (p : H →L[ℂ] H) (hp : IsStarProjection p) :
    NormedAddCommGroup (HilbertProjectionRange p hp) := inferInstanceAs (NormedAddCommGroup p.range)

instance hilbertProjectionRangeInner (p : H →L[ℂ] H) (hp : IsStarProjection p) :
    InnerProductSpace ℂ (HilbertProjectionRange p hp) := inferInstanceAs (InnerProductSpace ℂ p.range)

instance hilbertProjectionRangeComplete (p : H →L[ℂ] H) (hp : IsStarProjection p) :
    CompleteSpace (HilbertProjectionRange p hp) :=
  (ContinuousLinearMap.IsIdempotentElem.isClosed_range hp.isIdempotentElem).completeSpace_coe

def hilbertProjectionInclusion (p : H →L[ℂ] H) (hp : IsStarProjection p) :
    HilbertProjectionRange p hp →ₗᵢ[ℂ] H := p.range.subtypeₗᵢ

lemma hilbertProjectionInclusion_fixed (p : H →L[ℂ] H) (hp : IsStarProjection p)
    (x : HilbertProjectionRange p hp) : p (hilbertProjectionInclusion p hp x) =
      hilbertProjectionInclusion p hp x := by
  obtain ⟨y, hy⟩ := x.property
  change p x.val = x.val
  rw [← hy]
  exact congrArg (fun T : H →L[ℂ] H => T y) hp.isIdempotentElem.eq

lemma hilbertProjectionInclusion_adjoint (p : H →L[ℂ] H) (hp : IsStarProjection p) (x : H) :
    (hilbertProjectionInclusion p hp).toContinuousLinearMap.adjoint x =
      (⟨p x, x, rfl⟩ : HilbertProjectionRange p hp) := by
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ x (hilbertProjectionInclusion p hp y) =
    inner ℂ (p x) (hilbertProjectionInclusion p hp y)
  have hs : p.adjoint = p := hp.isSelfAdjoint.star_eq
  calc
    _ = inner ℂ x (p (hilbertProjectionInclusion p hp y)) := by
      rw [hilbertProjectionInclusion_fixed]
    _ = inner ℂ (p.adjoint x) (hilbertProjectionInclusion p hp y) :=
      (ContinuousLinearMap.adjoint_inner_left p _ x).symm
    _ = _ := congrArg (fun T : H →L[ℂ] H =>
      inner ℂ (T x) (hilbertProjectionInclusion p hp y)) hs

@[simp] lemma hilbertProjectionInclusion_projection (p : H →L[ℂ] H) (hp : IsStarProjection p) :
    isometricCornerProjection (hilbertProjectionInclusion p hp) = p := by
  ext x
  rw [isometricCornerProjection_apply, hilbertProjectionInclusion_adjoint]
  rfl

end WeakPureInfiniteness

end

end OAI
