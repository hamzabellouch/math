import OAI.Analysis.KadisonSimilarity.FreeProduct.TracialDihedralColumns
import Mathlib.Analysis.CStarAlgebra.Projection

namespace OAI

/-! The centered reflection used by the dihedral test is constructed from a
half-trace projection. Completing a smaller projection by an orthogonal
projection of the complementary trace supplies that projection; no centered
symmetry is assumed in this algebraic step. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P]

/-- The existing ring reflection is exactly the desired scalar formula. -/
theorem projectionReflection_eq_two_smul (p : P) :
    projectionReflection p = (2 : ℂ) • p - 1 := by
  unfold projectionReflection
  module

@[simp] theorem star_projectionReflection {p : P} (hp : IsStarProjection p) :
    star (projectionReflection p) = projectionReflection p :=
  projectionReflection_star p hp

@[simp] theorem projectionReflection_mul_self {p : P} (hp : IsStarProjection p) :
    projectionReflection p * projectionReflection p = 1 :=
  projectionReflection_sq p hp

/-- Taking the half projection of the constructed reflection recovers the
original projection exactly. -/
@[simp] theorem dihedralHalfProjection_projectionReflection {p : P}
    (hp : IsStarProjection p) :
    dihedralHalfProjection (symmetryUnit (projectionReflection p)
      (projectionReflection_mul_self hp)) = p := by
  change (1 / 2 : ℂ) • (1 + (p + p - 1)) = p
  module

theorem projectionReflection_mul_of_support {p e : P} (hpe : p * e = e) :
    projectionReflection p * e = e := by
  simp only [projectionReflection, sub_mul, add_mul, one_mul, hpe]
  abel

theorem mul_projectionReflection_of_support {p e : P} (hep : e * p = e) :
    e * projectionReflection p = e := by
  simp only [projectionReflection, mul_sub, mul_add, mul_one, hep]
  abel

/-- The exact half-projection identities consumed by the free-corner model. -/
theorem halfProjection_support_of_support {p e : P} (hp : IsStarProjection p)
    (hpe : p * e = e) (hep : e * p = e) :
    dihedralHalfProjection (symmetryUnit (projectionReflection p)
      (projectionReflection_mul_self hp)) * e = e ∧
    e * dihedralHalfProjection (symmetryUnit (projectionReflection p)
      (projectionReflection_mul_self hp)) = e := by
  rw [dihedralHalfProjection_projectionReflection hp]
  exact ⟨hpe, hep⟩

section Order
variable [PartialOrder P] [StarOrderedRing P]

/-- Order containment of projections gives the two required support identities. -/
theorem halfProjection_support_of_le {p e : P} (hp : IsStarProjection p)
    (he : IsStarProjection e) (hep : e ≤ p) :
    dihedralHalfProjection (symmetryUnit (projectionReflection p)
      (projectionReflection_mul_self hp)) * e = e ∧
    e * dihedralHalfProjection (symmetryUnit (projectionReflection p)
      (projectionReflection_mul_self hp)) = e :=
  halfProjection_support_of_support hp ((he.le_iff_mul_eq_right hp).mp hep)
    ((he.le_iff_mul_eq_left hp).mp hep)

end Order

/-- Minimal half-projection data, before constructing the reflection. The
existence of this data is supplied by projection completion in the intended
finite factor; the next constructor derives it from an actual complement. -/
structure HalfTraceProjectionData (τ : P →ₗ[ℂ] ℂ) (e : P) where
  projection : P
  isProjection : IsStarProjection projection
  trace_half : τ projection = (1 / 2 : ℂ)
  left_support : projection * e = e
  right_support : e * projection = e

/-- Completing a small corner by an orthogonal complement of the missing
trace produces a half-trace projection containing the original corner. -/
def halfTraceProjectionDataOfOrthogonal (τ : P →ₗ[ℂ] ℂ) {e q : P}
    (he : IsStarProjection e) (hq : IsStarProjection q) (heq : e * q = 0)
    {t : ℂ} (hetrace : τ e = t) (hqtrace : τ q = 1 / 2 - t) :
    HalfTraceProjectionData τ e where
  projection := e + q
  isProjection := he.add hq heq
  trace_half := by rw [map_add, hetrace, hqtrace]; ring
  left_support := by
    have hqe : q * e = 0 := by
      simpa only [star_mul, he.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq, star_zero]
        using congrArg star heq
    rw [add_mul, he.isIdempotentElem.eq, hqe, add_zero]
  right_support := by rw [mul_add, he.isIdempotentElem.eq, heq, add_zero]

namespace HalfTraceProjectionData

variable {τ : P →ₗ[ℂ] ℂ} {e : P} (Q : HalfTraceProjectionData τ e)

/-- The actual centered reflection obtained from the completed projection. -/
def reflection : P := projectionReflection Q.projection

@[simp] theorem reflection_star : star Q.reflection = Q.reflection :=
  star_projectionReflection Q.isProjection

@[simp] theorem reflection_square : Q.reflection * Q.reflection = 1 :=
  projectionReflection_mul_self Q.isProjection

theorem reflection_trace (hτ : τ 1 = 1) : τ Q.reflection = 0 :=
  trace_projectionReflection τ hτ Q.projection Q.trace_half

/-- Its half projection is the chosen completion, so all corner supports
are the original concrete multiplication identities. -/
theorem reflection_half :
    dihedralHalfProjection (symmetryUnit Q.reflection Q.reflection_square) = Q.projection :=
  dihedralHalfProjection_projectionReflection Q.isProjection

theorem reflection_support :
    dihedralHalfProjection (symmetryUnit Q.reflection Q.reflection_square) * e = e ∧
      e * dihedralHalfProjection (symmetryUnit Q.reflection Q.reflection_square) = e := by
  rw [Q.reflection_half]
  exact ⟨Q.left_support, Q.right_support⟩

theorem reflection_mul : Q.reflection * e = e ∧ e * Q.reflection = e :=
  ⟨projectionReflection_mul_of_support Q.left_support,
    mul_projectionReflection_of_support Q.right_support⟩

end HalfTraceProjectionData
end KadisonSimilarity

end

end OAI
