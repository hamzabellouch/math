import Mathlib
import OAI.Combinatorics.KMedian.Rounding.WeightedRounding
import OAI.Combinatorics.KMedian.Probability.ProbabilitySupport

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {T : Type*} [Fintype T] [DecidableEq T]

theorem target_subset_law (D : Finset T) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∃ μ : FiniteLaw (Finset T),
      (∀ S, 0 < μ.weight S → S ⊆ D ∧ |(S.card:ℝ)-(D.card:ℝ)*q| ≤ 1 ∧
        (q=0 → S=∅) ∧ (q=1 → S=D)) ∧
      ∀ t, μ.prob (fun S => t ∈ S) = if t ∈ D then q else 0 := by
  obtain ⟨μ, hcard, hm, _hp⟩ := WeightedRounding.exists_law
    (fun t => if t ∈ D then q else 0) (fun _t : T => (1:ℝ))
    (by intro t; split_ifs <;> positivity)
    (by intro t; split_ifs <;> linarith only [hq1])
    (by intro t; norm_num) (by intro t; exact le_rfl) (by norm_num)
  refine ⟨μ, ?_, hm⟩
  intro S hS
  have hsub : S ⊆ D := by
    intro t ht
    by_contra htd
    have hz : μ.prob (fun S => t ∈ S)=0 := by rw [hm, ite_eq_right htd]
    exact μ.prob_zero_support _ hz S hS ht
  refine ⟨hsub, ?_, ?_, ?_⟩
  · have hc := hcard S hS
    simpa only [sum_const, nsmul_eq_mul, mul_one, one_mul, sum_ite_mem, univ_inter,
      mul_comm] using hc
  · intro hq
    apply eq_empty_iff_forall_notMem.mpr
    intro t ht
    have hz : μ.prob (fun S => t ∈ S)=0 := by rw [hm, ite_eq_left (hsub ht), hq]
    exact μ.prob_zero_support _ hz S hS ht
  · intro hq
    apply Subset.antisymm hsub
    intro t ht
    have ho : μ.prob (fun S => t ∈ S)=1 := by rw [hm, ite_eq_left ht, hq]
    exact μ.prob_one_support _ ho S hS

end MetricKMedian.Preparation
end
end

end OAI
