import Mathlib
import OAI.Analysis.FreeWords.HaarLeftEndpoint
import OAI.Analysis.FreeWords.MatrixLeftEndpointDefinitions

namespace OAI

noncomputable section

namespace KKRelativeMatrix

noncomputable section

open Filter KKHaarEndpoints

open scoped Topology

variable {A:Type*} [Ring A] [StarRing A] [Algebra ℂ A]

theorem matrix_left_endpoint_limits : MatrixLeftEndpointLimits (A := A) := by
  intro ι L τ B u h1 htr hH hC n w hne hw a ha i j
  have hLeft := haar_left_endpoint_limits ι L τ B u h1 htr hH hC
  have hv (b c:Fin n) (v:List (ℤ×A)) (hmem:v∈entryWords w b c) :
      v≠[] ∧ CenteredPowerWord τ B v := by
    refine ⟨?_,?_⟩
    · intro he
      have hl := entryWords_length hmem
      rw [he,List.length_nil] at hl
      exact hne (List.eq_nil_of_length_eq_zero hl.symm)
    · intro z hz
      obtain ⟨q,hq,b,c,rfl⟩ := entryWords_letters hmem z hz
      exact ⟨(hw q hq).1,(hw q hq).2 b c⟩
  have hsum (b:Fin n) : Tendsto (fun t => τ (a i b*
      ((entryWords w b j).map (scalarWord (fun k => (u t^k).val))).sum)) L (𝓝 0) := by
    have haux : ∀v∈entryWords w b j,
        Tendsto (fun t => τ (a i b*scalarWord (fun k => (u t^k).val) v)) L (𝓝 0) := by
      intro v hm
      exact hLeft v (hv b j v hm).1 (hv b j v hm).2 (a i b) (ha i b)
    generalize he : entryWords w b j=l at haux ⊢
    clear he
    induction l with
    | nil => simpa using (tendsto_const_nhds : Tendsto (fun _:ι => (0:ℂ)) L (𝓝 0))
    | cons v l ih =>
      have hv0 := haux v List.mem_cons_self
      have hl0 := ih (fun z hz => haux z (List.mem_cons_of_mem _ hz))
      simpa only [List.map_cons,List.sum_cons,mul_add,map_add,add_zero] using hv0.add hl0
  have hh := tendsto_finsetSum Finset.univ (fun b _ => hsum b)
  simpa only [Matrix.mul_apply,entryWords_sum,map_sum,Finset.sum_const_zero] using hh

end

end KKRelativeMatrix
end

end OAI
