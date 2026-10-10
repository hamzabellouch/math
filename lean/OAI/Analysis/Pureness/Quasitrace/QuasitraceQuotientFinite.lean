import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientCFC

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

include hsqrt

lemma cauchyQuotient_isometry_unitary (x : T.CauchyQuotient hadd) (hx : star x*x = 1) :
    x*star x = 1 := by
  let p := x*star x
  have hp : IsSelfAdjoint p := IsSelfAdjoint.mul_star_self x
  have hpp : p*p = p := by
    change (x*star x)*(x*star x) = x*star x
    calc
      _ = x*(star x*x)*star x := by noncomm_ring
      _ = _ := by rw [hx]; simp
  let e := 1-p
  have he : IsSelfAdjoint e := by
    change star (1-p) = 1-p
    simp only [star_sub,star_one,hp.star_eq]
  have hee : star e*e = e := by
    rw [he.star_eq]
    change (1-p)*(1-p) = 1-p
    noncomm_ring [hpp]
  have hvalue : T.quotientValue hadd hsqrt e = 0 := by
    have hv := T.quotientValue_polar hadd hsqrt x
    rw [hx] at hv
    have hc := T.quotientValue_one_sub hadd hsqrt ⟨p,hp⟩
    change T.quotientValue hadd hsqrt e = T.quotientValue hadd hsqrt 1-T.quotientValue hadd hsqrt p at hc
    rw [hc,hv,sub_self]
  have he0 : e = 0 := (T.quotientValue_square_eq_zero_iff hadd hsqrt e).mp (by rw [hee,hvalue])
  exact (sub_eq_zero.mp he0).symm
end CuntzPureness.PositiveQuasitrace

end

end OAI
