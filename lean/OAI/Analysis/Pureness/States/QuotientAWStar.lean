import OAI.Analysis.Pureness.States.QuotientAnnihilatorMaximum

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexOrder
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

include hsqrt in
lemma exists_quotient_left_support (y : T.CauchyQuotient hadd) :
    ∃ p : T.CauchyQuotient hadd, IsStarProjection p ∧ p*y=y ∧
      ∀ a, a*y=0 ↔ a*p=0 := by
  obtain ⟨e,hsa,hid,hann⟩ := T.quotient_principal_right_annihilator hadd hsqrt (star y)
  have he : IsStarProjection e := ⟨hid,hsa⟩
  have hye : star y*e=0 := (hann e).mpr hid
  have hey : e*y=0 := by
    simpa only [star_mul,star_star,hsa.star_eq,star_zero] using congrArg star hye
  have hpy : (1-e)*y=y := by rw [sub_mul,one_mul,hey,sub_zero]
  refine ⟨1-e,he.one_sub,hpy,?_⟩
  intro a
  constructor
  · intro hay
    have hya : star y*star a=0 := by simpa only [star_mul,star_zero] using congrArg star hay
    have hea := (hann (star a)).mp hya
    have hae : a*e=a := by
      simpa only [star_mul,star_star,hsa.star_eq] using congrArg star hea
    rw [mul_sub,mul_one,hae,sub_self]
  · intro hap
    calc
      a*y = a*((1-e)*y) := by rw [hpy]
      _ = 0 := by rw [← mul_assoc,hap,zero_mul]

include hsqrt in

theorem quotient_right_annihilator_projection (S : Set (T.CauchyQuotient hadd)) :
    ∃ p : T.CauchyQuotient hadd, IsStarProjection p ∧
      ∀ y, (∀ a ∈ S, a*y=0) ↔ p*y=y := by
  obtain ⟨p,hp,hpann,hmax⟩ := T.exists_quotient_annihilator_maximum hadd hsqrt S
  refine ⟨p,hp,?_⟩
  intro y
  constructor
  · intro hy
    obtain ⟨q,hq,hqy,hann⟩ := T.exists_quotient_left_support hadd hsqrt y
    have hqp : q ≤ p := hmax q hq (fun a ha => (hann a).mp (hy a ha))
    have hpq := (hq.le_iff_mul_eq_right hp).mp hqp
    calc
      p*y = p*(q*y) := by rw [hqy]
      _ = y := by rw [← mul_assoc,hpq,hqy]
  · intro hpy a ha
    calc
      a*y = a*(p*y) := by rw [hpy]
      _ = 0 := by rw [← mul_assoc,hpann a ha,zero_mul]

include hsqrt in

theorem quotient_right_annihilator_range (S : Set (T.CauchyQuotient hadd)) :
    ∃ p : T.CauchyQuotient hadd, IsStarProjection p ∧
      ∀ y, (∀ a ∈ S, a*y=0) ↔ ∃ z, y=p*z := by
  obtain ⟨p,hp,hann⟩ := T.quotient_right_annihilator_projection hadd hsqrt S
  refine ⟨p,hp,?_⟩
  intro y
  rw [hann y]
  constructor
  · intro h; exact ⟨y,h.symm⟩
  · rintro ⟨z,rfl⟩
    rw [← mul_assoc,hp.isIdempotentElem.eq]
end CuntzPureness.PositiveQuasitrace

end

end OAI
