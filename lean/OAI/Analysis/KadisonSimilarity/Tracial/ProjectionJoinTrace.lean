import OAI.Analysis.KadisonSimilarity.Representation.NormalSupportTransport
import OAI.Analysis.KadisonSimilarity.Tracial.TracialRightSupportDischarge

namespace OAI

/-! Finite joins of projections and their trace bound. These elementary
support identities are used to control countable unions of small spectral
projections in the normal representation argument. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance joinTrace_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (M : Set (H →L[ℂ] H))
  infer_instance

/-- A positive trace is monotone in the algebraic projection order. -/
theorem trace_projection_le {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (τ : A →ₚ[ℂ] ℂ)
    (p q : A) (hp : IsStarProjection p) (hq : IsStarProjection q)
    (h : q * p = p) : (τ p).re ≤ (τ q).re := by
  have ht := τ.map_nonneg (hp.sub_of_mul_eq_right hq h).nonneg
  rw [map_sub] at ht
  exact sub_nonneg.mp ht.1

/-- The range support has trace at most that of a prescribed right support. -/
theorem trace_normalRangeSupport_le (M : VonNeumannAlgebra H)
    (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (htr : ∀ a b, τ (a * b) = τ (b * a))
    (x p : M.toStarSubalgebra) (hp : IsStarProjection p) (hxp : x * p = x) :
    (τ (normalRangeSupport M x)).re ≤ (τ p).re := by
  have hpx : p * star x = star x := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq] using congrArg star hxp
  obtain ⟨r, hr, hrt, hxr⟩ := exists_rightSupport_trace_le M τ htr p (star x) hp hpx
  have hrx : r * x = x := by
    simpa only [star_mul, star_star, hr.isSelfAdjoint.star_eq] using congrArg star hxr
  exact (trace_projection_le τ _ _ (normalRangeSupport_isStarProjection M x) hr
    (normalRangeSupport_least M x r hrx)).trans hrt

/-- Join formed from the orthogonal part of the second projection. -/
def projectionJoin (M : VonNeumannAlgebra H) (p q : M.toStarSubalgebra) :
    M.toStarSubalgebra := p + normalRangeSupport M ((1 - p) * q)

theorem projectionJoin_properties (M : VonNeumannAlgebra H)
    (p q : M.toStarSubalgebra) (hp : IsStarProjection p) (_hq : IsStarProjection q) :
    IsStarProjection (projectionJoin M p q) ∧
      projectionJoin M p q * p = p ∧ projectionJoin M p q * q = q ∧
      ∀ r : M.toStarSubalgebra, r * p = p → r * q = q →
        r * projectionJoin M p q = projectionJoin M p q := by
  let x := (1 - p) * q
  let s := normalRangeSupport M x
  have hs : IsStarProjection s := normalRangeSupport_isStarProjection M x
  have hpx : p * x = 0 := by
    dsimp [x]
    rw [← mul_assoc, mul_sub, mul_one, hp.isIdempotentElem.eq, sub_self, zero_mul]
  have hps : p * s = 0 := by
    apply Subtype.ext
    exact mul_rangeSupport_eq_zero (x : H →L[ℂ] H) p (congrArg Subtype.val hpx)
  have hsp : s * p = 0 := by
    simpa only [star_mul, hp.isSelfAdjoint.star_eq, hs.isSelfAdjoint.star_eq, star_zero]
      using congrArg star hps
  have hsx : s * x = x := normalRangeSupport_mul M x
  have hsq : s * q = x := by
    calc
      s * q = (s * (1 - p)) * q := by rw [mul_sub, mul_one, hsp, sub_zero]
      _ = s * x := mul_assoc _ _ _
      _ = x := hsx
  refine ⟨hp.add hs hps, ?_, ?_, ?_⟩
  · change (p + s) * p = p
    rw [add_mul, hp.isIdempotentElem.eq, hsp, add_zero]
  · change (p + s) * q = q
    rw [add_mul, hsq]
    dsimp [x]
    rw [sub_mul, one_mul]
    abel
  · intro r hrp hrq
    have hrx : r * x = x := by
      dsimp [x]
      rw [sub_mul, one_mul, mul_sub, ← mul_assoc, hrp, hrq]
    have hrs : r * s = s := normalRangeSupport_least M x r hrx
    change r * (p + s) = p + s
    rw [mul_add, hrp, hrs]

/-- Subadditivity of the trace for a finite projection join. -/
theorem trace_projectionJoin_le (M : VonNeumannAlgebra H)
    (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ)
    (htr : ∀ a b, τ (a * b) = τ (b * a))
    (p q : M.toStarSubalgebra) (hq : IsStarProjection q) :
    (τ (projectionJoin M p q)).re ≤ (τ p).re + (τ q).re := by
  have hright : ((1 - p) * q) * q = (1 - p) * q := by
    rw [mul_assoc, hq.isIdempotentElem.eq]
  have ht := trace_normalRangeSupport_le M τ htr ((1 - p) * q) q hq hright
  change (τ (p + normalRangeSupport M ((1 - p) * q))).re ≤ _
  rw [map_add, Complex.add_re]
  linarith

end KadisonSimilarity

end

end OAI
