import Mathlib
import OAI.Analysis.Commutator.ProjectionEquivalence
import OAI.Analysis.Commutator.ProjectionShift

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem subEquivalent_antisymm (M : VonNeumannAlgebra H)
    {e f : H →L[ℂ] H} (heM : e∈M) (he : IsStarProjection e) (hf : IsStarProjection f)
    (hef : SubEquivalent M e f) (hfe : SubEquivalent M f e) : Equivalent M e f := by
  obtain ⟨u,hu⟩ := hef
  obtain ⟨v,hv⟩ := hfe
  let a := u.val
  let b := v.val
  let w := b*a
  let p := e-v.final
  have hai : star a*a=e := hu
  have hbi : star b*b=f := hv
  have hea : a*e=a := u.mul_source he
  have hfa : f*a=a := u.target_mul hf
  have heb : e*b=b := v.target_mul he
  have hbf : b*f=b := v.mul_source hf
  have hve : v.final*e=v.final := (v.final_projection.le_iff_mul_eq_left he).mp v.target_le
  have hp : IsStarProjection p := v.final_projection.sub_of_mul_eq_left he hve
  have hw : star w*w=e := by
    calc
      _=star a*(star b*b)*a := by simp only [w,star_mul]; noncomm_ring
      _=e := by rw [hbi,mul_assoc,hfa,hai]
  have hwe : w*e=w := by dsimp [w]; rw [mul_assoc,hea]
  have hew : e*w=w := by dsimp [w]; rw [←mul_assoc,heb]
  have hpw : p*w=0 := by
    change (e-v.final)*(b*a)=0
    rw [←mul_assoc,sub_mul,heb]
    have hvb : v.final*b=b := v.final_mul
    rw [hvb,sub_self,zero_mul]
  have hbound : p+w*star w≤e := by
    have hh : w*star w≤v.final := by
      calc
        _=b*u.final*star b := by simp only [w,Link.final,star_mul]; noncomm_ring
        _≤b*f*star b := star_right_conjugate_le_conjugate u.target_le b
        _=v.final := by rw [hbf]; rfl
    exact (add_le_add le_rfl hh).trans_eq (sub_add_cancel e v.final)
  obtain ⟨q,hqM,hq,hqe,hfix⟩ := ProjectionShift.exists_fixed_projection M he hp hw hwe hpw hbound
    (M.mul_mem v.mem u.mem) (M.sub_mem heM (M.mul_mem v.mem (M.star_mem' v.mem)))
  have heq : e*q=q := (hq.le_iff_mul_eq_right he).mp hqe
  have hqe' : q*e=q := (hq.le_iff_mul_eq_left he).mp hqe
  have hpq : p≤q := by
    rw [hfix]
    exact le_add_of_nonneg_right (star_right_conjugate_nonneg hq.nonneg w)
  have hpq' : p*q=p := (hp.le_iff_mul_eq_left hq).mp hpq
  have hqp : q*p=p := (hp.le_iff_mul_eq_right hq).mp hpq
  have hqw : q*w=w*q := by
    calc
      _=(p+w*q*star w)*w := by rw [←hfix]
      _=w*q*(star w*w) := by rw [add_mul,hpw,zero_add]; noncomm_ring
      _=w*q := by rw [hw,mul_assoc,hqe']
  have hcross : (e-q)*w*q=0 := by
    calc
      _=w*q-(w*q)*q := by rw [sub_mul,sub_mul,hew,hqw]
      _=0 := by rw [mul_assoc w q q,hq.isIdempotentElem.eq,sub_self]
  have hcross' : q*star w*(e-q)=0 := by
    simpa only [star_mul,star_sub,he.isSelfAdjoint.star_eq,hq.isSelfAdjoint.star_eq,star_zero,mul_assoc]
      using congrArg star hcross
  have hrem : (e-q)*(b*star b)=e-q := by
    have hb : b*star b=e-p := by dsimp [p,Link.final,b]; noncomm_ring
    rw [hb]
    have hpe : p*e=p := (hp.le_iff_mul_eq_left he).mp (hpq.trans hqe)
    have hep : e*p=p := (hp.le_iff_mul_eq_right he).mp (hpq.trans hqe)
    calc
      _=e*e-e*p-q*e+q*p := by noncomm_ring
      _=e-q := by rw [he.isIdempotentElem.eq,hep,hqe',hqp]; abel
  let r := a*q+star b*(e-q)
  have hri : star r*r=e := by
    have hs : star r=q*star a+(e-q)*b := by
      dsimp [r]
      simp only [star_add,star_mul,star_sub,star_star,hq.isSelfAdjoint.star_eq,he.isSelfAdjoint.star_eq]
    calc
      _=(q*(star a*a)*q)+(q*star w*(e-q))+((e-q)*w*q)+((e-q)*(b*star b)*(e-q)) := by
        rw [hs]; dsimp [r,w]; simp only [star_mul]; noncomm_ring
      _=q+(e-q)*(e-q) := by
        rw [hai,mul_assoc q e q,heq,hq.isIdempotentElem.eq,hcross',hcross,hrem,add_zero,add_zero]
      _=e := by
        have hremP := hq.sub_of_mul_eq_left he hqe'
        rw [hremP.isIdempotentElem.eq]; abel
  have hconj : star b*q*b=a*q*star a := by
    calc
      _=star b*(p+w*q*star w)*b := by rw [←hfix]
      _=star b*e*b-(star b*b)*(star b*b)+(star b*b)*a*q*star a*(star b*b) := by
        dsimp [p,w,Link.final,b]; simp only [star_mul]; noncomm_ring
      _=a*q*star a := by
        have hsa : star a*f=star a := by
          simpa only [star_mul,hf.isSelfAdjoint.star_eq] using congrArg star hfa
        rw [mul_assoc (star b) e b,heb,hbi,hf.isIdempotentElem.eq,sub_self,zero_add,hfa]
        rw [mul_assoc (a*q) (star a) f,hsa]
  have hrf : r*star r=f := by
    have hqq : q*(e-q)=0 := by rw [mul_sub,hqe',hq.isIdempotentElem.eq,sub_self]
    have hqq' : (e-q)*q=0 := by rw [sub_mul,heq,hq.isIdempotentElem.eq,sub_self]
    calc
      _=a*(q*q)*star a+a*(q*(e-q))*b+star b*((e-q)*q)*star a+star b*((e-q)*(e-q))*b := by
        dsimp [r]; simp only [star_add,star_mul,star_sub,star_star,hq.isSelfAdjoint.star_eq,he.isSelfAdjoint.star_eq]
        noncomm_ring
      _=a*q*star a+star b*(e-q)*b := by
        rw [hq.isIdempotentElem.eq,hqq,hqq',mul_zero,zero_mul,mul_zero,zero_mul,add_zero,add_zero,
          (hq.sub_of_mul_eq_left he hqe').isIdempotentElem.eq]
      _=f := by
        rw [mul_sub,sub_mul,hconj,mul_assoc (star b) e b,heb,hbi]; abel
  have hre : r*e=r := by
    dsimp [r]
    have hrq : (e-q)*e=e-q := by rw [sub_mul,he.isIdempotentElem.eq,hqe']
    rw [add_mul,mul_assoc a q e,hqe',mul_assoc (star b) (e-q) e,hrq]
  exact ⟨⟨r,M.add_mem (M.mul_mem u.mem hqM) (M.mul_mem (M.star_mem' v.mem) (M.sub_mem heM hqM)),
    by rw [mul_assoc,hri,hre],hri.le,hrf.le⟩,hri,hrf⟩

end Kadison.PartialIsometryOrder

end

end
end

end OAI
