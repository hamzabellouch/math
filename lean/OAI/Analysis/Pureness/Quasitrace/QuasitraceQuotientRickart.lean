import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientAnnihilator

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexOrder
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

lemma quotient_square_right_annihilator (x y : T.CauchyQuotient hadd) :
    (star x*x)*y=0 ↔ x*y=0 := by
  constructor
  · intro h
    have hz : star (x*y)*(x*y)=0 := by
      calc
        star (x*y)*(x*y) = star y*((star x*x)*y) := by simp only [star_mul,mul_assoc]
        _ = 0 := by rw [h,mul_zero]
    exact (CStarRing.star_mul_self_eq_zero_iff (x*y)).mp hz
  · intro h
    rw [mul_assoc,h,mul_zero]

include hsqrt in

lemma quotient_principal_right_annihilator (x : T.CauchyQuotient hadd) :
    ∃ e : T.CauchyQuotient hadd, IsSelfAdjoint e ∧ e*e=e ∧
      ∀ y, x*y=0 ↔ e*y=y := by
  obtain ⟨p,hsa,hid,_,hann,_⟩ := T.exists_quotient_support_annihilator hadd hsqrt (Positive.starMul x)
  refine ⟨1-p,(show IsSelfAdjoint (1-p) from by
    change star (1-p)=1-p
    rw [star_sub,star_one,hsa.star_eq]),?_,?_⟩
  · calc
      (1-p)*(1-p) = 1-p-p+p*p := by noncomm_ring
      _ = 1-p := by rw [hid]; abel
  · intro y
    have ha := hann y
    change (star x*x)*y=0 ↔ p*y=0 at ha
    rw [← T.quotient_square_right_annihilator hadd x y,ha]
    constructor
    · intro h
      rw [sub_mul,one_mul,h,sub_zero]
    · intro h
      rw [sub_mul,one_mul] at h
      exact sub_eq_self.mp h
end CuntzPureness.PositiveQuasitrace

end

end OAI
