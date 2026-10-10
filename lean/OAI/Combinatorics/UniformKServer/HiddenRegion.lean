import Mathlib
import OAI.Combinatorics.UniformKServer.HiddenFlow

namespace OAI

                                   
section

/-! Posterior counting mass of any genuinely causal finite region. -/
noncomputable section
namespace UniformKServer.HiddenFlow
open Finset ConditionalLaw
open scoped Classical
variable {X Ω : Type*} [Fintype Ω] {k : ℕ}

def regionCount (D : Data X Ω k) (R : ℕ→Ω→Finset X) (t : ℕ) (ω : Ω) : ℝ :=
  ∑ a : Fin k,if D.position t ω a∈R t ω then 1 else 0

theorem regionCount_range (D : Data X Ω k) (R : ℕ→Ω→Finset X) (t : ℕ) (ω : Ω) :
    regionCount D R t ω∈Set.Icc 0 (k:ℝ) := by
  constructor
  · exact sum_nonneg (fun a _=>by split_ifs <;> norm_num)
  · calc
      _≤∑ a : Fin k,(1:ℝ) := sum_le_sum (fun a _=>by split_ifs <;> norm_num)
      _=_ := by simp

theorem regionCount_eq (D : Data X Ω k) (t : ℕ) (ω : Ω) (R : Finset X) :
    (∑ p∈R,counts D t ω p)=∑ a : Fin k,if D.position t ω a∈R then (1:ℝ) else 0 := by
  unfold counts
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  simp [atom]

theorem region_posterior (D : Data X Ω k) (R : ℕ→Ω→Finset X)
    (hR : ∀ t ω v,(D.filtration t).r ω v→R t ω=R t v) (t : ℕ) (ω : Ω) :
    posterior D.weight (D.filtration t) (regionCount D R t) ω=
      ∑ p∈R t ω,current D t ω p := by
  unfold posterior
  have he (v : Ω) : kernel D.weight (D.filtration t) ω v*regionCount D R t v=
      kernel D.weight (D.filtration t) ω v*∑ p∈R t ω,counts D t v p := by
    by_cases hv : (D.filtration t).r ω v
    · rw [regionCount_eq, hR t ω v hv]
      rfl
    · simp only [kernel,ite_eq_right hv,zero_mul]
  simp_rw [he,mul_sum]
  rw [sum_comm]
  rfl

end UniformKServer.HiddenFlow

end


end

end OAI
