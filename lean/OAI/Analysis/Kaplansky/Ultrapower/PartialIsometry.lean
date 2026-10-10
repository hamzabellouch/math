import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.StableFiniteness.Definitions

namespace OAI

noncomputable section

namespace KaplanskyConsequences
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

def IsPartialIsometry (v : A) : Prop := v*star v*v=v
namespace IsPartialIsometry
variable {v w : A}
lemma star_op (hv : IsPartialIsometry v) : IsPartialIsometry (star v) := by
  have h := congrArg Star.star hv
  simpa only [IsPartialIsometry,star_mul,star_star,mul_assoc] using h
lemma initial (hv : IsPartialIsometry v) : IsStarProjection (star v*v) := by
  refine ⟨?_,(star_mul_self_nonneg _).isSelfAdjoint⟩
  change (star v*v)*(star v*v)=star v*v
  calc _ = star v*(v*star v*v) := by noncomm_ring
       _ = _ := by rw [hv]
lemma final (hv : IsPartialIsometry v) : IsStarProjection (v*star v) := by
  simpa only [star_star] using hv.star_op.initial
lemma norm_le (hv : IsPartialIsometry v) : ‖v‖ ≤ 1 := by
  have h := hv.initial.norm_le
  rw [CStarRing.norm_star_mul_self] at h
  nlinarith [norm_nonneg v]
lemma zero : IsPartialIsometry (0 : A) := by simp [IsPartialIsometry]
lemma of_initial (h : IsStarProjection (star v*v)) : IsPartialIsometry v := by
  have hz : star (v*star v*v-v)*(v*star v*v-v)=0 := by
    simp only [star_sub,star_mul,star_star]
    calc
      _ = (star v*v)*(star v*v)*(star v*v)-(star v*v)*(star v*v)-
        (star v*v)*(star v*v)+star v*v := by noncomm_ring
      _ = 0 := by simp only [h.isIdempotentElem.eq,sub_self,zero_sub,neg_add_cancel]
  exact sub_eq_zero.mp ((CStarRing.star_mul_self_eq_zero_iff _).mp hz)
lemma mul_initial (hv : IsPartialIsometry v) : v*(star v*v)=v := by
  simpa only [IsPartialIsometry,mul_assoc] using hv
lemma final_mul (hv : IsPartialIsometry v) : (v*star v)*v=v := hv
lemma mul_initial_compl (hv : IsPartialIsometry v) : v*(1-star v*v)=0 := by
  rw [mul_sub,mul_one,hv.mul_initial,sub_self]
lemma final_compl_mul (hv : IsPartialIsometry v) : (1-v*star v)*v=0 := by
  rw [sub_mul,one_mul,hv.final_mul,sub_self]
lemma initial_compl_mul_star (hv : IsPartialIsometry v) : (1-star v*v)*star v=0 := by
  simpa only [star_mul,star_sub,star_one,star_star,star_zero,mul_assoc] using congrArg Star.star hv.mul_initial_compl
lemma star_mul_final_compl (hv : IsPartialIsometry v) : star v*(1-v*star v)=0 := by
  simpa only [star_mul,star_sub,star_one,star_star,star_zero] using congrArg Star.star hv.final_compl_mul

lemma add_orthogonal (hv : IsPartialIsometry v) (hw : IsPartialIsometry w)
    (hvw : star v*w=0) (hvw' : v*star w=0) : IsPartialIsometry (v+w) := by
  have hwv : star w*v=0 := by simpa only [star_mul,star_star,star_zero] using congrArg Star.star hvw
  have hwv' : w*star v=0 := by simpa only [star_mul,star_star,star_zero] using congrArg Star.star hvw'
  change (v+w)*star (v+w)*(v+w)=v+w
  simp only [star_add,add_mul,mul_add,hvw',hwv',zero_add,add_zero]
  simp only [mul_assoc,hvw,hwv,mul_zero,zero_add,add_zero,
    hv.mul_initial,hw.mul_initial]

lemma initial_of_factor {x : A} (hv : IsPartialIsometry v)
    (hf : v*CFC.sqrt (star x*x)=x) : (star v*v)*CFC.sqrt (star x*x)=CFC.sqrt (star x*x) := by
  let b := CFC.sqrt (star x*x)
  have hb : IsSelfAdjoint b := (CFC.sqrt_nonneg _).isSelfAdjoint
  have hbb : b*b=star x*x := CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg x)
  have he : b*(star v*v)*b=b*b := by
    calc _ = star (v*b)*(v*b) := by rw [star_mul,hb.star_eq]; noncomm_ring
         _ = star x*x := by rw [hf]
         _ = _ := hbb.symm
  have hz : star ((1-star v*v)*b)*((1-star v*v)*b)=0 := by
    rw [star_mul,hv.initial.one_sub.isSelfAdjoint.star_eq,hb.star_eq]
    calc _ = b*((1-star v*v)*(1-star v*v))*b := by noncomm_ring
         _ = b*(1-star v*v)*b := by rw [hv.initial.one_sub.isIdempotentElem.eq]
         _ = b*b-b*(star v*v)*b := by noncomm_ring
         _ = 0 := by rw [he,sub_self]
  have hh := (CStarRing.star_mul_self_eq_zero_iff _).mp hz
  rw [sub_mul,one_mul] at hh
  exact (sub_eq_zero.mp hh).symm
end IsPartialIsometry

end KaplanskyConsequences

end

end OAI
