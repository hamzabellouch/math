import Mathlib
import OAI.Analysis.Commutator.FactorCorner
import OAI.Analysis.Commutator.PartialIsometryMaximal

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Link

variable {M : VonNeumannAlgebra H} {e f : H →L[ℂ] H}

lemma residual_source_projection (v : Link M e f) (he : IsStarProjection e) :
    IsStarProjection (e-v.initial) :=
  v.initial_projection.sub_of_mul_eq_left he
    ((v.initial_projection.le_iff_mul_eq_left he).mp v.source_le)

lemma residual_target_projection (v : Link M e f) (hf : IsStarProjection f) :
    IsStarProjection (f-v.final) :=
  v.final_projection.sub_of_mul_eq_left hf
    ((v.final_projection.le_iff_mul_eq_left hf).mp v.target_le)

lemma residual_mul_initial (v : Link M e f) (he : IsStarProjection e)
    (w : Link M (e-v.initial) (f-v.final)) : w.val*v.initial=0 := by
  have hep := (v.initial_projection.le_iff_mul_eq_right he).mp v.source_le
  calc
    _=(w.val*(e-v.initial))*v.initial := by
      rw [w.mul_source (v.residual_source_projection he)]
    _=0 := by rw [mul_assoc,sub_mul,hep,v.initial_projection.isIdempotentElem.eq,sub_self,mul_zero]

lemma final_mul_residual (v : Link M e f) (hf : IsStarProjection f)
    (w : Link M (e-v.initial) (f-v.final)) : v.final*w.val=0 := by
  have hqf := (v.final_projection.le_iff_mul_eq_left hf).mp v.target_le
  calc
    _=v.final*((f-v.final)*w.val) := by
      rw [w.target_mul (v.residual_target_projection hf)]
    _=0 := by rw [←mul_assoc,mul_sub,hqf,v.final_projection.isIdempotentElem.eq,sub_self,zero_mul]

lemma residual_cross (v : Link M e f) (he : IsStarProjection e) (hf : IsStarProjection f)
    (w : Link M (e-v.initial) (f-v.final)) :
    star v.val*w.val=0 ∧ v.val*star w.val=0 := by
  constructor
  · have hstar := congrArg star v.final_mul
    simp only [star_mul,v.final_projection.isSelfAdjoint.star_eq] at hstar
    calc
      _=(star v.val*v.final)*w.val := by rw [hstar]
      _=0 := by rw [mul_assoc,v.final_mul_residual hf w,mul_zero]
  · have hstar := congrArg star (v.residual_mul_initial he w)
    simp only [star_mul,v.initial_projection.isSelfAdjoint.star_eq,star_zero] at hstar
    calc
      _=(v.val*v.initial)*star w.val := by rw [v.mul_initial]
      _=0 := by rw [mul_assoc,hstar,mul_zero]

def extend (v : Link M e f) (he : IsStarProjection e) (hf : IsStarProjection f)
    (w : Link M (e-v.initial) (f-v.final)) : Link M e f := by
  have hvw := (v.residual_cross he hf w).1
  have hvw' := (v.residual_cross he hf w).2
  have hwv : star w.val*v.val=0 := by simpa only [star_mul,star_star,star_zero] using congrArg star hvw
  have hwv' : w.val*star v.val=0 := by simpa only [star_mul,star_star,star_zero] using congrArg star hvw'
  have hinit : star (v.val+w.val)*(v.val+w.val)=v.initial+w.initial := by
    simp only [star_add,add_mul,mul_add,hvw,hwv,add_zero,zero_add,initial]
  have hfinal : (v.val+w.val)*star (v.val+w.val)=v.final+w.final := by
    simp only [star_add,add_mul,mul_add,hvw',hwv',add_zero,zero_add,final]
  refine ⟨v.val+w.val,M.add_mem v.mem w.mem,?_,?_,?_⟩
  · rw [star_add]
    simp only [add_mul,mul_add,hvw',hwv',zero_add,add_zero]
    rw [v.triple,w.triple]
    have h1 : v.val*star v.val*w.val=0 := by rw [mul_assoc,hvw,mul_zero]
    have h2 : w.val*star w.val*v.val=0 := by rw [mul_assoc,hwv,mul_zero]
    rw [h1,h2,add_zero,zero_add]
  · rw [hinit]
    calc
      _ ≤ v.initial+(e-v.initial) := add_le_add_right w.source_le _
      _=e := by abel
  · rw [hfinal]
    calc
      _ ≤ v.final+(f-v.final) := add_le_add_right w.target_le _
      _=f := by abel

@[simp] lemma extend_val (v : Link M e f) (he : IsStarProjection e) (hf : IsStarProjection f)
    (w : Link M (e-v.initial) (f-v.final)) : (v.extend he hf w).val=v.val+w.val := rfl

lemma le_extend (v : Link M e f) (he : IsStarProjection e) (hf : IsStarProjection f)
    (w : Link M (e-v.initial) (f-v.final)) : v≤v.extend he hf w := by
  obtain ⟨hvw,_⟩ := v.residual_cross he hf w
  have hwv : star w.val*v.val=0 := by simpa only [star_mul,star_star,star_zero] using congrArg star hvw
  apply (le_def _ _).mpr
  constructor
  · change v.initial ≤ star (v.val+w.val)*(v.val+w.val)
    simp only [star_add,add_mul,mul_add,hvw,hwv,add_zero,zero_add]
    exact le_add_of_nonneg_right w.initial_projection.nonneg
  · change (v.val+w.val)*v.initial=v.val
    rw [add_mul,v.mul_initial,v.residual_mul_initial he w,add_zero]

end Link

theorem factor_comparison (M : VonNeumannAlgebra H) (hM : FactorCorner.IsFactor M)
    {e f : H →L[ℂ] H} (heM : e∈M) (hfM : f∈M)
    (he : IsStarProjection e) (hf : IsStarProjection f) :
    ∃ v : Link M e f, v.initial=e ∨ v.final=f := by
  obtain ⟨v,hv⟩ := exists_maximal M he hf
  refine ⟨v,?_⟩
  by_contra h
  have hresE : e-v.initial≠0 := fun hh => h (Or.inl (sub_eq_zero.mp hh).symm)
  have hresF : f-v.final≠0 := fun hh => h (Or.inr (sub_eq_zero.mp hh).symm)
  have hmemE : e-v.initial∈M := M.sub_mem heM (M.mul_mem (M.star_mem' v.mem) v.mem)
  have hmemF : f-v.final∈M := M.sub_mem hfM (M.mul_mem v.mem (M.star_mem' v.mem))
  obtain ⟨w,hwM,hwn,hwt,hwi,hwf⟩ := FactorCorner.exists_linking_partialIsometry M hM
    hmemE hmemF (v.residual_source_projection he) (v.residual_target_projection hf) hresE hresF
  let w' : Link M (e-v.initial) (f-v.final) := ⟨w,hwM,hwt,hwi,hwf⟩
  have hvu := v.le_extend he hf w'
  have heq : v.extend he hf w'=v := le_antisymm (hv hvu) hvu
  have hval := congrArg Link.val heq
  change v.val+w=v.val at hval
  exact hwn (add_left_cancel (hval.trans (add_zero v.val).symm))

end Kadison.PartialIsometryOrder

end

end
end

end OAI
