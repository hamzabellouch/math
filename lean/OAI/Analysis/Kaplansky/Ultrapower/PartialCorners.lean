import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.Ultrapower.PartialIsometry

namespace OAI

noncomputable section

namespace KaplanskyConsequences
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]
namespace IsPartialIsometry
variable {v w z : A}
lemma extension_initial (hv : IsPartialIsometry v) (hw : IsPartialIsometry w)
    (h : w*(star v*v)=v) : (star w*w)*(star v*v)=star v*v := by
  let p := star v*v
  let q := star w*w
  have hp : IsStarProjection p := hv.initial
  have hq : IsStarProjection q := hw.initial
  have hh : p*q*p=p := by
    calc _ = star (w*p)*(w*p) := by rw [star_mul,hp.isSelfAdjoint.star_eq]; dsimp [q]; noncomm_ring
         _ = _ := by rw [h]
  have hz : star ((1-q)*p)*((1-q)*p)=0 := by
    rw [star_mul,hp.isSelfAdjoint.star_eq,hq.one_sub.isSelfAdjoint.star_eq]
    calc _ = p*((1-q)*(1-q))*p := by noncomm_ring
         _ = p*(1-q)*p := by rw [hq.one_sub.isIdempotentElem.eq]
         _ = p*p-p*q*p := by noncomm_ring
         _ = 0 := by rw [hp.isIdempotentElem.eq,hh,sub_self]
  have he := (CStarRing.star_mul_self_eq_zero_iff _).mp hz
  rw [sub_mul,one_mul] at he
  exact (sub_eq_zero.mp he).symm

lemma orthogonal_of_corners (hw : IsPartialIsometry w)
    (hl : (1-w*star w)*z=z) (hr : z*(1-star w*w)=z) :
    star w*z=0 ∧ w*star z=0 := by
  constructor
  · calc _ = star w*((1-w*star w)*z) := by rw [hl]
         _ = (star w*(1-w*star w))*z := by noncomm_ring
         _ = 0 := by rw [hw.star_mul_final_compl,zero_mul]
  · have hzs : z*star w=0 := by
      calc _ = (z*(1-star w*w))*star w := by rw [hr]
           _ = z*((1-star w*w)*star w) := by noncomm_ring
           _ = 0 := by rw [hw.initial_compl_mul_star,mul_zero]
    simpa only [star_mul,star_star,star_zero] using congrArg Star.star hzs

lemma corner_annihilates_extension (hv : IsPartialIsometry v) (hw : IsPartialIsometry w)
    (h : w*(star v*v)=v) (hr : z*(1-star w*w)=z) : z*(star v*v)=0 := by
  have hi := extension_initial hv hw h
  calc _ = (z*(1-star w*w))*(star v*v) := by rw [hr]
       _ = z*((1-star w*w)*(star v*v)) := by noncomm_ring
       _ = 0 := by rw [sub_mul,one_mul,hi,sub_self,mul_zero]
end IsPartialIsometry

end KaplanskyConsequences

end

end OAI
