import Mathlib
import OAI.Analysis.Commutator.FactorComparison

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def IsFiniteAlgebra (M : VonNeumannAlgebra H) : Prop :=
  ∀ v∈M,star v*v=1 → v*star v=1

lemma IsFiniteAlgebra.coisometry {M : VonNeumannAlgebra H} (hM : IsFiniteAlgebra M)
    {v : H →L[ℂ] H} (hv : v∈M) (h : v*star v=1) : star v*v=1 := by
  simpa only [star_star] using hM (star v) (M.star_mem' hv) (by simpa only [star_star] using h)

lemma finite_corner_cancel {M : VonNeumannAlgebra H} (hM : IsFiniteAlgebra M)
    {e : H →L[ℂ] H} (heM : e∈M) (he : IsStarProjection e)
    (v : Link M e e) (hve : v.initial=e) : v.final=e := by
  let r := 1-e
  have hr : IsStarProjection r := he.one_sub
  have hvr : v.val*r=0 := by
    change v.val*(1-e)=0
    rw [mul_sub,mul_one,v.mul_source he,sub_self]
  have hrv : r*v.val=0 := by
    change (1-e)*v.val=0
    rw [sub_mul,one_mul,v.target_mul he,sub_self]
  have hsvr : star v.val*r=0 := by
    simpa only [star_mul,hr.isSelfAdjoint.star_eq,star_zero] using congrArg star hrv
  have hrsv : r*star v.val=0 := by
    simpa only [star_mul,hr.isSelfAdjoint.star_eq,star_zero] using congrArg star hvr
  have hi : star (v.val+r)*(v.val+r)=1 := by
    rw [star_add,hr.isSelfAdjoint.star_eq,add_mul,mul_add,mul_add,hsvr,hrv,
      hr.isIdempotentElem.eq,add_zero,zero_add]
    change v.initial+(1-e)=1
    rw [hve]; abel
  have hf := hM (v.val+r) (M.add_mem v.mem (M.sub_mem M.one_mem heM)) hi
  rw [star_add,hr.isSelfAdjoint.star_eq,add_mul,mul_add,mul_add,hvr,hrsv,
    hr.isIdempotentElem.eq,add_zero,zero_add] at hf
  change v.final+(1-e)=1 at hf
  have := congrArg (fun x : H →L[ℂ] H => x-(1-e)) hf
  have hc : (1 : H →L[ℂ] H)-(1-e)=e := by abel
  simpa only [add_sub_cancel_right,hc] using this

namespace Link

variable {M : VonNeumannAlgebra H} {e f : H →L[ℂ] H}

lemma extend_initial (v : Link M e f) (he : IsStarProjection e) (hf : IsStarProjection f)
    (w : Link M (e-v.initial) (f-v.final)) : (v.extend he hf w).initial=v.initial+w.initial := by
  obtain ⟨hvw,_⟩ := v.residual_cross he hf w
  have hwv : star w.val*v.val=0 := by simpa only [star_mul,star_star,star_zero] using congrArg star hvw
  change star (v.val+w.val)*(v.val+w.val)=v.initial+w.initial
  simp only [star_add,add_mul,mul_add,hvw,hwv,add_zero,zero_add,initial]

lemma extend_final (v : Link M e f) (he : IsStarProjection e) (hf : IsStarProjection f)
    (w : Link M (e-v.initial) (f-v.final)) : (v.extend he hf w).final=v.final+w.final := by
  obtain ⟨_,hvw⟩ := v.residual_cross he hf w
  have hwv : w.val*star v.val=0 := by simpa only [star_mul,star_star,star_zero] using congrArg star hvw
  change (v.val+w.val)*star (v.val+w.val)=v.final+w.final
  simp only [star_add,add_mul,mul_add,hvw,hwv,add_zero,zero_add,final]

end Link

theorem finite_unitary_extension (M : VonNeumannAlgebra H)
    (hfac : FactorCorner.IsFactor M) (hfin : IsFiniteAlgebra M)
    {p q : H →L[ℂ] H} (hpM : p∈M) (hqM : q∈M)
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (v : Link M p q) (hvi : v.initial=p) (hvf : v.final=q) :
    ∃ u∈M,star u*u=1 ∧ u*star u=1 ∧ u*p=v.val := by
  let b : Link M 1 1 := ⟨v.val,v.mem,v.triple,v.source_le.trans hp.le_one,v.target_le.trans hq.le_one⟩
  have hbi : b.initial=p := hvi
  have hbf : b.final=q := hvf
  have hiM : 1-b.initial∈M := by rw [hbi]; exact M.sub_mem M.one_mem hpM
  have hfM : 1-b.final∈M := by rw [hbf]; exact M.sub_mem M.one_mem hqM
  obtain ⟨w,hw⟩ := factor_comparison M hfac hiM hfM
    (b.residual_source_projection (IsStarProjection.one _))
    (b.residual_target_projection (IsStarProjection.one _))
  let z := b.extend (IsStarProjection.one _) (IsStarProjection.one _) w
  have hz : z.initial=1 ∧ z.final=1 := by
    rcases hw with hw|hw
    · have he : z.initial=1 := by
        rw [show z.initial=b.initial+w.initial from b.extend_initial _ _ w,hw]; abel
      exact ⟨he,hfin z.val z.mem he⟩
    · have he : z.final=1 := by
        rw [show z.final=b.final+w.final from b.extend_final _ _ w,hw]; abel
      exact ⟨hfin.coisometry z.mem he,he⟩
  refine ⟨z.val,z.mem,hz.1,hz.2,?_⟩
  simpa only [hbi] using (b.le_extend (IsStarProjection.one _) (IsStarProjection.one _) w).2

end Kadison.PartialIsometryOrder

end

end
end

end OAI
