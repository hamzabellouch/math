import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder ContinuousFunctionalCalculus

namespace Kadison.CFCIntertwiner

variable {A : Type*} [CStarAlgebra A]

local instance : ContinuousFunctionalCalculus ℂ (A × A) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

local instance : ContinuousFunctionalCalculus ℝ (A × A) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

lemma semiconj_cfc (x a b : A) (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (h : x*a=b*x) (f : ℝ → ℝ) (hf : Continuous f) :
    x*cfc f a=cfc f b*x := by
  have hab : IsSelfAdjoint (a,b) := Prod.ext ha hb
  have hc : ∀ g : C(spectrum ℝ (a,b),ℝ),
      x*(cfcHom hab g).1=(cfcHom hab g).2*x := by
    intro g
    induction g using ContinuousMap.induction_on_of_compact with
    | const r =>
      change x*((cfcHom hab) (algebraMap ℝ _ r)).1=((cfcHom hab) (algebraMap ℝ _ r)).2*x
      rw [AlgHomClass.commutes]
      change x*algebraMap ℝ A r=algebraMap ℝ A r*x
      exact (Algebra.commutes r x).symm
    | id => simpa only [cfcHom_id] using h
    | star_id => simpa only [map_star,cfcHom_id,Prod.fst_star,Prod.snd_star,ha.star_eq,hb.star_eq] using h
    | add g k hg hk => simp only [map_add,Prod.fst_add,Prod.snd_add,mul_add,add_mul,hg,hk]
    | mul g k hg hk =>
      simp only [map_mul,Prod.fst_mul,Prod.snd_mul]
      calc
        x*((cfcHom hab g).1*(cfcHom hab k).1)=
          (x*(cfcHom hab g).1)*(cfcHom hab k).1 := (mul_assoc ..).symm
        _=((cfcHom hab g).2*x)*(cfcHom hab k).1 := by rw [hg]
        _=(cfcHom hab g).2*((cfcHom hab k).2*x) := by rw [mul_assoc,hk]
        _=((cfcHom hab g).2*(cfcHom hab k).2)*x := (mul_assoc ..).symm
    | frequently g hg =>
      have closed : IsClosed {k : C(spectrum ℝ (a,b),ℝ) |
          x*(cfcHom hab k).1=(cfcHom hab k).2*x} :=
        isClosed_eq ((cfcHom_continuous hab).fst.const_mul x)
          ((cfcHom_continuous hab).snd.mul_const x)
      exact closed.mem_of_frequently_of_tendsto hg Filter.tendsto_id
  have hh : x*(cfc f (a,b)).1=(cfc f (a,b)).2*x := by
    rw [cfc_apply f (a,b) hab hf.continuousOn]
    exact hc _
  rw [cfc_map_prod (S := ℂ) f a b hf.continuousOn hab ha hb] at hh
  exact hh

end Kadison.CFCIntertwiner

end

end
end

end OAI
