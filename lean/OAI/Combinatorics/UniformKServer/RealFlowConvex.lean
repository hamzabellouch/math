import Mathlib
import OAI.Combinatorics.UniformKServer.RealFlow

namespace OAI

noncomputable section

/-! Convexity is at the actual causal flow level, not at the nonlinear row
normalization level. -/
namespace UniformKServer.RealFlow
open Finset
open scoped Classical
variable {R C J : Type*} [Fintype C] [Fintype J]

def combine (a b : ℝ) (F G : Data R C J) : Data R C J where
  mass w c := a*F.mass w c+b*G.mass w c
  flow w r c j := a*F.flow w r c j+b*G.flow w r c j

theorem combine_valid (F G : Data R C J) (T : C→R→J→C)
    (allowed : C→R→J→Prop) (s : C) (H : ℕ)
    (hF : Valid F T allowed s H) (hG : Valid G T allowed s H)
    (a b : ℝ) (ha : 0≤a) (hb : 0≤b) (hab : a+b=1) :
    Valid (combine a b F G) T allowed s H := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro w hw c
    exact add_nonneg (mul_nonneg ha (hF.mass_nonneg w hw c)) (mul_nonneg hb (hG.mass_nonneg w hw c))
  · intro w hw
    simp only [combine,sum_add_distrib,←mul_sum,hF.mass_total w hw,hG.mass_total w hw,mul_one,hab]
  · intro c
    simp only [combine,hF.initial,hG.initial]
    split_ifs <;> simp only [mul_one,hab,mul_zero,add_zero]
  · intro w hw r c j
    exact add_nonneg (mul_nonneg ha (hF.flow_nonneg w hw r c j)) (mul_nonneg hb (hG.flow_nonneg w hw r c j))
  · intro w hw r c j hj
    simp only [combine,hF.support w hw r c j hj,hG.support w hw r c j hj,mul_zero,add_zero]
  · intro w hw r c
    simp only [combine,sum_add_distrib,←mul_sum,hF.outflow w hw,hG.outflow w hw]
  · intro w hw r c'
    have he (c : C) (j : J) : (if T c r j=c' then (combine a b F G).flow w r c j else 0)=
        a*(if T c r j=c' then F.flow w r c j else 0)+
        b*(if T c r j=c' then G.flow w r c j else 0) := by
      split_ifs <;> simp only [combine,mul_zero,add_zero]
    simp_rw [he]
    simp only [sum_add_distrib,←mul_sum,hF.inflow w hw,hG.inflow w hw,combine]

theorem combine_cost (F G : Data R C J) (a b : ℝ) (d : C→R→J→ℝ) (w u : List R) :
    flowCost (combine a b F G) d w u=a*flowCost F d w u+b*flowCost G d w u := by
  induction u generalizing w with
  | nil => simp only [flowCost,mul_zero,add_zero]
  | cons r u ih =>
    rw [flowCost,ih,flowCost,flowCost]
    simp only [combine,add_mul,mul_assoc,sum_add_distrib,←mul_sum]
    ring

end UniformKServer.RealFlow

end

end OAI
