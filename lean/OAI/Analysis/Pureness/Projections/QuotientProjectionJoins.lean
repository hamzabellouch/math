import OAI.Analysis.Pureness.Projections.QuotientProjectionLimits
import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientRickart

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexOrder
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

lemma quotient_projection_add_annihilator {p q : T.CauchyQuotient hadd}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (y : T.CauchyQuotient hadd) :
    (p+q)*y=0 ↔ p*y=0 ∧ q*y=0 := by
  have he : star (p*y)*(p*y)+star (q*y)*(q*y) = star y*((p+q)*y) := by
    calc
      _ = star y*(p*p)*y+star y*(q*q)*y := by
        simp only [star_mul,hp.isSelfAdjoint.star_eq,hq.isSelfAdjoint.star_eq]
        noncomm_ring
      _ = _ := by rw [hp.isIdempotentElem.eq,hq.isIdempotentElem.eq]; noncomm_ring
  constructor
  · intro h
    rw [h,mul_zero] at he
    have hzero := (add_eq_zero_iff_of_nonneg (star_mul_self_nonneg (p*y))
      (star_mul_self_nonneg (q*y))).mp he
    exact ⟨(CStarRing.star_mul_self_eq_zero_iff _).mp hzero.1,
      (CStarRing.star_mul_self_eq_zero_iff _).mp hzero.2⟩
  · rintro ⟨h₁,h₂⟩
    rw [add_mul,h₁,h₂,add_zero]

include hsqrt in

lemma exists_quotient_projection_join {p q : T.CauchyQuotient hadd}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    ∃ r : T.CauchyQuotient hadd, IsStarProjection r ∧ p ≤ r ∧ q ≤ r ∧
      (∀ y, r*y=0 ↔ p*y=0 ∧ q*y=0) ∧
      (∀ y, y*r=0 ↔ y*p=0 ∧ y*q=0) := by
  obtain ⟨r,hsa,hid,_,ha,_⟩ := T.exists_quotient_support_annihilator hadd hsqrt
    ⟨p+q,add_nonneg hp.nonneg hq.nonneg⟩
  have hr : IsStarProjection r := ⟨hid,hsa⟩
  have hann (y : T.CauchyQuotient hadd) : r*y=0 ↔ p*y=0 ∧ q*y=0 :=
    (ha y).symm.trans (T.quotient_projection_add_annihilator hadd hp hq y)
  have he := (hann (1-r)).mp hr.mul_one_sub_self
  have hpr : p ≤ r := (hp.le_iff_mul_eq_left hr).mpr (by
    have h := he.1
    rw [mul_sub,mul_one,sub_eq_zero] at h
    exact h.symm)
  have hqr : q ≤ r := (hq.le_iff_mul_eq_left hr).mpr (by
    have h := he.2
    rw [mul_sub,mul_one,sub_eq_zero] at h
    exact h.symm)
  refine ⟨r,hr,hpr,hqr,hann,?_⟩
  intro y
  have h := hann (star y)
  have hz (e : T.CauchyQuotient hadd) (hsa : IsSelfAdjoint e) :
      e*star y=0 ↔ y*e=0 := by
    constructor <;> intro heq
    · simpa only [star_mul,star_star,hsa.star_eq,star_zero] using congrArg star heq
    · simpa only [star_mul,star_star,hsa.star_eq,star_zero] using congrArg star heq
  simpa only [hz r hr.isSelfAdjoint,hz p hp.isSelfAdjoint,hz q hq.isSelfAdjoint] using h

lemma quotient_projection_eq_of_le_of_value_le {p q : T.CauchyQuotient hadd}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p ≤ q)
    (hv : (T.quotientValue hadd hsqrt q).re ≤ (T.quotientValue hadd hsqrt p).re) : p=q := by
  have hd := (hp.le_iff_sub hq).mp hpq
  have he := T.quotientValue_sub_commute hadd hsqrt
    ⟨q,hq.isSelfAdjoint⟩ ⟨p,hp.isSelfAdjoint⟩ (hp.commute_of_le hq hpq).symm
  have hn := (Complex.nonneg_iff.mp (T.quotientValue_nonneg hadd hsqrt ⟨q-p,hd.nonneg⟩)).1
  have hz : T.quotientValue hadd hsqrt (q-p)=0 := by
    apply Complex.ext
    · have hre := congrArg Complex.re he
      simp only [Complex.sub_re] at hre
      simp only [Complex.zero_re]
      linarith
    · exact T.quotientValue_selfAdjoint_im hadd hsqrt ⟨q-p,hd.isSelfAdjoint⟩
  have hs : star (q-p)*(q-p)=q-p := by rw [hd.isSelfAdjoint.star_eq,hd.isIdempotentElem.eq]
  have hzero := (T.quotientValue_square_eq_zero_iff hadd hsqrt (q-p)).mp (by rw [hs,hz])
  exact (sub_eq_zero.mp hzero).symm
end CuntzPureness.PositiveQuasitrace

end

end OAI
