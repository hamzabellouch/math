import OAI.Analysis.KadisonSimilarity.Representation.SpectralStepDischarge

namespace OAI

/-! Range supports are preserved by star isomorphisms between concrete von
Neumann algebras. The proof uses their algebraic least-support property, so
no continuity in the weak operator topology is assumed. -/

noncomputable section
namespace KadisonSimilarity

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Any left identity on an operator is a left identity on its range support. -/
theorem rangeSupport_least_left (B p : H →L[ℂ] H) (h : p * B = B) :
    p * rangeSupport B = rangeSupport B := by
  have hz : (1 - p) * B = 0 := by rw [sub_mul, one_mul, h, sub_self]
  have hs := mul_rangeSupport_eq_zero B (1 - p) hz
  rw [sub_mul, one_mul, sub_eq_zero] at hs
  exact hs.symm

/-- The range support viewed as an element of its original normal algebra. -/
def normalRangeSupport (M : VonNeumannAlgebra H) (a : M.toStarSubalgebra) :
    M.toStarSubalgebra := ⟨rangeSupport (a : H →L[ℂ] H), rangeSupport_mem M a a.property⟩

theorem normalRangeSupport_isStarProjection (M : VonNeumannAlgebra H)
    (a : M.toStarSubalgebra) : IsStarProjection (normalRangeSupport M a) := by
  constructor
  · apply Subtype.ext
    exact (rangeSupport_isStarProjection (a : H →L[ℂ] H)).isIdempotentElem.eq
  · apply Subtype.ext
    exact (rangeSupport_isStarProjection (a : H →L[ℂ] H)).isSelfAdjoint.star_eq

theorem normalRangeSupport_mul (M : VonNeumannAlgebra H) (a : M.toStarSubalgebra) :
    normalRangeSupport M a * a = a := by
  apply Subtype.ext
  exact rangeSupport_mul (a : H →L[ℂ] H)

theorem normalRangeSupport_least (M : VonNeumannAlgebra H)
    (a p : M.toStarSubalgebra) (h : p * a = a) :
    p * normalRangeSupport M a = normalRangeSupport M a := by
  apply Subtype.ext
  exact rangeSupport_least_left (a : H →L[ℂ] H) p (congrArg Subtype.val h)

/-- Isomorphisms preserve support projections by their leastness in the
algebraic projection order. -/
theorem normalRangeSupport_map
    (M : VonNeumannAlgebra H) (N : VonNeumannAlgebra K)
    (e : M.toStarSubalgebra ≃⋆ₐ[ℂ] N.toStarSubalgebra) (a : M.toStarSubalgebra) :
    e (normalRangeSupport M a) = normalRangeSupport N (e a) := by
  let p := e (normalRangeSupport M a)
  let q := normalRangeSupport N (e a)
  have hp : IsStarProjection p := (normalRangeSupport_isStarProjection M a).map e
  have hq : IsStarProjection q := normalRangeSupport_isStarProjection N (e a)
  have hpa : p * e a = e a := by
    change e (normalRangeSupport M a) * e a = e a
    rw [← map_mul e, normalRangeSupport_mul]
  have hpq : p * q = q := normalRangeSupport_least N (e a) p hpa
  have hqa : e.symm q * a = a := by
    apply e.injective
    calc
      e (e.symm q * a) = e (e.symm q) * e a := e.map_mul' _ _
      _ = q * e a := congrArg (fun b => b * e a) (e.apply_symm_apply q)
      _ = e a := normalRangeSupport_mul N (e a)
  have hqp : q * p = p := by
    have h := congrArg e (normalRangeSupport_least M a (e.symm q) hqa)
    simpa only [map_mul, e.apply_symm_apply] using h
  have hpq' : q * p = q := by
    have h := congrArg star hpq
    simpa only [star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq] using h
  exact hqp.symm.trans hpq'

end KadisonSimilarity

end

end OAI
