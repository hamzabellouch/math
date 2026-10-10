import OAI.Analysis.Pureness.Projections.QuotientNonzeroSpectralCorner
import OAI.Analysis.Pureness.Projections.SpectralCornerPartialIsometry

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace
open scoped Topology NNReal ENNReal ComplexOrder
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

include hsqrt in

theorem quotient_equivalent_subprojections_of_nonzero_corner
    (p q : T.CauchyQuotient hadd) (hp : IsStarProjection p) (hq : IsStarProjection q)
    (z : T.CauchyQuotient hadd) (hz : z ≠ 0) (hpz : p*z=z) (hzq : z*q=z) :
    ∃ v : T.CauchyQuotient hadd,
      IsStarProjection (star v*v) ∧ IsStarProjection (v*star v) ∧
      star v*v ≠ 0 ∧ v*star v ≠ 0 ∧ star v*v ≤ q ∧ v*star v ≤ p := by
  let a : Positive (T.CauchyQuotient hadd) := ⟨star z*z,star_mul_self_nonneg z⟩
  have ha : a.1 ≠ 0 := fun h => hz ((CStarRing.star_mul_self_eq_zero_iff z).mp h)
  have hqa : q*a.1=a.1 := by
    have hqz : q*star z=star z := by
      simpa only [star_mul, hq.isSelfAdjoint.star_eq] using congrArg star hzq
    change q*(star z*z)=star z*z
    rw [← mul_assoc, hqz]
  obtain ⟨t,e,ht,he,he0,heq,hec,hel⟩ := T.exists_quotient_nonzero_spectral_corner hadd hsqrt a ha q hq hqa
  obtain ⟨v,hv,hve,hleft⟩ := exists_partial_isometry_of_spectral_lower_bound z e he hec t ht hel
  have hrange := partial_isometry_range_projection v e hve hv p hp (hleft p hpz)
  have hv0 : v ≠ 0 := by
    intro hz
    apply he0
    rw [← hv, hz, star_zero, zero_mul]
  have hg0 : v*star v ≠ 0 := by
    intro hg
    have h : star v=0 := (CStarRing.star_mul_self_eq_zero_iff (star v)).mp (by
      simpa only [star_star] using hg)
    exact hv0 (star_eq_zero.mp h)
  exact ⟨v,hv.symm ▸ he,hrange.1,hv.symm ▸ he0,hg0,hv.symm ▸ heq,hrange.2⟩
end CuntzPureness.PositiveQuasitrace

end

end OAI
