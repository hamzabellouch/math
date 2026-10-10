import Mathlib

namespace OAI

namespace MetricKMedian
open Finset

structure RationalLaw (Ω : Type) [Fintype Ω] where
  weight : Ω → ℚ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω=1

namespace RationalLaw
variable {Ω I : Type} [Fintype Ω] [Fintype I]

theorem compress (μ : RationalLaw Ω) (feature : Ω → I → ℚ) :
    ∃ (Ξ : Type) (inst : Fintype Ξ), letI := inst;
      ∃ (ν : RationalLaw Ξ) (state : Ξ → Ω),
        Fintype.card Ξ ≤ Fintype.card I+1 ∧
        ∀ i, (∑ ξ, ν.weight ξ*feature (state ξ) i)=∑ ω, μ.weight ω*feature ω i := by
  let x : I → ℚ := ∑ ω, μ.weight ω • feature ω
  have hx : x ∈ convexHull ℚ (Set.range feature) := by
    apply (convex_convexHull ℚ (Set.range feature)).sum_mem
      (fun ω _ => μ.nonneg ω) μ.total
    intro ω _
    exact subset_convexHull ℚ (Set.range feature) (Set.mem_range_self ω)
  obtain ⟨Ξ,inst,z,w,hz,hi,hw,hs,hx'⟩ := eq_pos_convex_span_of_mem_convexHull hx
  let := inst
  choose state hstate using fun ξ => hz (Set.mem_range_self ξ)
  let ν : RationalLaw Ξ := ⟨w,fun ξ => (hw ξ).le,hs⟩
  refine ⟨Ξ,inst,ν,state,?_,?_⟩
  · have hc := hi.card_le_finrank_succ
    have hd : Module.finrank ℚ (vectorSpan ℚ (Set.range z)) ≤ Fintype.card I := by
      exact (Submodule.finrank_le _).trans_eq (Module.finrank_fintype_fun_eq_card ℚ)
    exact hc.trans (Nat.add_le_add_right hd 1)
  · intro i
    have he := congrFun hx' i
    simpa only [x,ν,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,← hstate] using he

end RationalLaw
end MetricKMedian

end OAI
