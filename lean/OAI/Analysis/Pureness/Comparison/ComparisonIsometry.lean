import OAI.Analysis.Pureness.Comparison.Comparison
import OAI.Analysis.Pureness.Comparison.FullnessFrame

namespace OAI
open scoped CStarAlgebra
namespace CuntzComparison
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem exists_isometry_of_one_cuntzSubequiv {b : A} (hb : 0 ≤ b)
    (hcomp : CuntzSubequiv 1 b) :
    ∃ w x z : A, IsSelfAdjoint z ∧ w = CFC.sqrt b * x * z ∧
      star w * w = 1 ∧ IsStarProjection (w * star w) ∧
      w * star w = CFC.sqrt b * (x * (z * z) * star x) * CFC.sqrt b := by
  obtain ⟨x, hx⟩ := cuntzSubequiv_iff_norm.mp hcomp 1 zero_lt_one
  let t := star x * b * x
  have ht : 0 ≤ t := star_left_conjugate_nonneg hb x
  have htu : IsUnit t := by
    have hnorm : ‖1 - t‖ < 1 := by simpa only [norm_sub_rev] using hx
    have h := (Units.oneSub (1 - t) hnorm).isUnit
    change IsUnit (1 - (1 - t)) at h
    simpa only [sub_sub_cancel] using h
  have htp : IsStrictlyPositive t := IsStrictlyPositive.iff_of_unital.mpr ⟨ht, htu⟩
  let z := CFC.rpow t (-(1 / 2) : ℝ)
  have hz : IsSelfAdjoint z := .of_nonneg CFC.rpow_nonneg
  have hs : IsSelfAdjoint (CFC.sqrt b) := .of_nonneg (CFC.sqrt_nonneg b)
  have hztz : z * t * z = 1 := CFC.conjugate_rpow_neg_one_half t htp
  let w := CFC.sqrt b * x * z
  have hw : star w * w = 1 :=
    normalized_isometry hs hz (CFC.sqrt_mul_sqrt_self b hb) hztz
  obtain ⟨hsa, hid⟩ := isometry_range_projection hw
  refine ⟨w, x, z, hz, rfl, hw, ⟨hid, hsa⟩, ?_⟩
  simp only [w, star_mul, hz.star_eq, hs.star_eq, mul_assoc]

omit [StarOrderedRing A] in
theorem TracialState.trace_isometry_range (τ : TracialState A) {w : A}
    (hw : star w * w = 1) : τ.toPositiveLinearMap (w * star w) = 1 := by
  rw [τ.tracial, hw, τ.normalized]

end CuntzComparison

end OAI
