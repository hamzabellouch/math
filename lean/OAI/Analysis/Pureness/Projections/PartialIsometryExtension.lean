import OAI.Analysis.Pureness.Projections.SpectralCornerPartialIsometry

namespace OAI
noncomputable section
namespace CuntzPureness
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

omit [PartialOrder D] [StarOrderedRing D] in
theorem partial_isometry_mul_initial (v : D) (hv : IsStarProjection (star v*v)) :
    v*(star v*v)=v := by
  let e := star v*v
  have he : e*e=e := hv.isIdempotentElem.eq
  have hz : star (v-v*e)*(v-v*e)=0 := by
    calc
      _ = e-e*e-e*e+(e*e)*e := by
        dsimp [e]
        simp only [star_sub,star_mul,star_star]
        noncomm_ring
      _ = 0 := by simp only [he]; abel
  exact (sub_eq_zero.mp ((CStarRing.star_mul_self_eq_zero_iff _).mp hz)).symm

theorem partial_isometry_norm_le_one (v : D) (hv : IsStarProjection (star v*v)) : ‖v‖ ≤ 1 := by
  have he : ‖star v*v‖ ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hv.nonneg).mpr
    (sub_nonneg.mp hv.one_sub.nonneg)
  rw [CStarRing.norm_star_mul_self] at he
  nlinarith [norm_nonneg v]

theorem partial_isometry_extension_square
    (u v : D) (hu : IsStarProjection (star u*u)) (hv : IsStarProjection (star v*v))
    (hle : star u*u ≤ star v*v) (hext : v*(star u*u)=u) :
    star (v-u)*(v-u)=star v*v-star u*u := by
  have he : (star v*v)*(star u*u)=star u*u := (hu.le_iff_mul_eq_right hv).mp hle
  have hcross : star v*u=star u*u := by
    calc
      star v*u = star v*(v*(star u*u)) := congrArg (fun z => star v*z) hext.symm
      _ = star u*u := by rw [← mul_assoc,he]
  have hcross' : star u*v=star u*u := by
    simpa only [star_mul,star_star,hu.isSelfAdjoint.star_eq] using congrArg star hcross
  rw [star_sub,sub_mul,mul_sub,mul_sub,hcross,hcross']
  abel
end CuntzPureness

end

end OAI
