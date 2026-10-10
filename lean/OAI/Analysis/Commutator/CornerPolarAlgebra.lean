import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.CornerPolarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma square_root_defect_le {q a : A} (hq : IsStarProjection q)
    (ha : 0≤a) (haq : a*q=a) :
    star (q-a)*(q-a) ≤ star (q-a*a)*(q-a*a) := by
  have has := (IsSelfAdjoint.of_nonneg ha).star_eq
  have hqa : q*a=a := by
    simpa only [star_mul,has,hq.isSelfAdjoint.star_eq] using congrArg star haq
  have hc : Commute q a := hqa.trans haq.symm
  have hsub : IsSelfAdjoint (q-a) := hq.isSelfAdjoint.sub (IsSelfAdjoint.of_nonneg ha)
  have hs : 0≤(q-a)*(q-a) := by
    simpa only [hsub.star_eq] using star_mul_self_nonneg (q-a)
  have hasc : Commute a ((q-a)*(q-a)) :=
    (hc.symm.sub_right (Commute.refl a)).mul_right (hc.symm.sub_right (Commute.refl a))
  have hqa' : Commute (q-a) q := (Commute.refl q).sub_left hc.symm
  have hscq : Commute ((q-a)*(q-a)) q := hqa'.mul_left hqa'
  have hc' : Commute (a*((q-a)*(q-a))) (a+(q+q)) :=
    ((Commute.refl a).mul_left hasc.symm).add_right
      ((hc.symm.mul_left hscq).add_right (hc.symm.mul_left hscq))
  have hpos : 0≤a*((q-a)*(q-a))*(a+(q+q)) :=
    Commute.mul_nonneg (Commute.mul_nonneg ha hs hasc)
      (add_nonneg ha (add_nonneg hq.nonneg hq.nonneg)) hc'
  have he : star (q-a*a)*(q-a*a)-star (q-a)*(q-a)=
      a*((q-a)*(q-a))*(a+(q+q)) := by
    simp only [star_sub,star_mul,has,hq.isSelfAdjoint.star_eq]
    have hqaa : q*(a*a)=a*a := by rw [←mul_assoc,hqa]
    noncomm_ring [hq.isIdempotentElem.eq,hqa,haq,hqaa]
  exact sub_nonneg.mp (he.symm ▸ hpos)

lemma polar_defect_le {q r a v : A} (hq : IsStarProjection q)
    (hr : IsStarProjection r) (hrq : r≤q) (ha : 0≤a)
    (hra : r*a=a) (haq : a*q=a) (hv : star v*v=r) :
    star (v-v*a)*(v-v*a) ≤ star (q-a*a)*(q-a*a) := by
  have has := (IsSelfAdjoint.of_nonneg ha).star_eq
  have har : a*r=a := by
    simpa only [star_mul,has,hr.isSelfAdjoint.star_eq] using congrArg star hra
  have hqa : q*a=a := by
    simpa only [star_mul,has,hq.isSelfAdjoint.star_eq] using congrArg star haq
  have he : star (v-v*a)*(v-v*a)=star (q-a)*(q-a)-(q-r) := by
    simp only [star_sub,star_mul,has,hq.isSelfAdjoint.star_eq]
    have hva : star v*(v*a)=a := by rw [←mul_assoc,hv,hra]
    noncomm_ring [hq.isIdempotentElem.eq,hra,har,hqa,haq,hv,hva]
  rw [he]
  exact (sub_le_self _ (sub_nonneg.mpr hrq)).trans (square_root_defect_le hq ha haq)

lemma kernel_defect_le {q r a : A} (hq : IsStarProjection q)
    (hr : IsStarProjection r) (ha : 0≤a) (hra : r*a=a) (haq : a*q=a) :
    q-r ≤ star (q-a*a)*(q-a*a) := by
  have has := (IsSelfAdjoint.of_nonneg ha).star_eq
  have har : a*r=a := by
    simpa only [star_mul,has,hr.isSelfAdjoint.star_eq] using congrArg star hra
  have hqa : q*a=a := by
    simpa only [star_mul,has,hq.isSelfAdjoint.star_eq] using congrArg star haq
  have he : star (q-a*a)*(q-a*a)-(q-r)=star (r-a*a)*(r-a*a) := by
    simp only [star_sub,star_mul,has,hq.isSelfAdjoint.star_eq,hr.isSelfAdjoint.star_eq]
    have hqaa : q*(a*a)=a*a := by rw [←mul_assoc,hqa]
    have hraa : r*(a*a)=a*a := by rw [←mul_assoc,hra]
    noncomm_ring [hq.isIdempotentElem.eq,hr.isIdempotentElem.eq,hqa,haq,hra,har,hqaa,hraa]
  exact sub_nonneg.mp (he.symm ▸ star_mul_self_nonneg (r-a*a))

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_partial_isometry_le {r v : A} (hr : IsStarProjection r)
    (hv : star v*v=r) : ‖v‖≤1 := by
  have hnorm : ‖star v*v‖=‖v‖*‖v‖ := CStarRing.norm_star_mul_self
  rw [hv] at hnorm
  have hrnorm := hr.norm_le r
  nlinarith [norm_nonneg v]

end Kadison.CornerPolarAlgebra

end

end
end

end OAI
