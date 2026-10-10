import Mathlib
import OAI.Combinatorics.UniformKServer.StarLocalCharges

namespace OAI

                                   
section

/-! All-time movement of the causal allocator, including its separate feasible
initial state. There is exactly one initial allowance, not one per epoch. -/
noncomputable section
namespace UniformKServer.StarAllSteps
open Finset StarRanks StarSchedules StarAllocator StarLocalCharges AllocationOutputs
open scoped Classical
variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

theorem size_move (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) {q₀ q₁ : ℝ}
    (h₀ : StarLower.parentLower d t ω ≤ q₀) (h₁ : StarLower.parentLower d (t+1) ω ≤ q₁) :
    variation (output d hk t ω q₀) (output d hk (t+1) ω q₁) ≤
      120*((∑ i, held d t ω i)+(∑ i, held d (t+1) ω i)) := by
  unfold variation
  calc
    _ ≤ ∑ i, (output d hk (t+1) ω q₁ i+output d hk t ω q₀ i) := by
      apply sum_le_sum
      intro i _
      have h := abs_sub (output d hk (t+1) ω q₁ i) (output d hk t ω q₀ i)
      simpa only [abs_of_nonneg (nonneg d hk (t+1) ω h₁ i),abs_of_nonneg (nonneg d hk t ω h₀ i)] using h
    _ ≤ ∑ i, (120*held d (t+1) ω i+120*held d t ω i) := by
      apply sum_le_sum
      intro i _
      exact add_le_add (((feasible d hk (t+1) ω h₁).2.1 i).trans (StarCaps.cap_bound d hk (t+1) ω i))
        (((feasible d hk t ω h₀).2.1 i).trans (StarCaps.cap_bound d hk t ω i))
    _ = _ := by rw [sum_add_distrib,←mul_sum,←mul_sum]; ring

def expense (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) : ℝ :=
  4*endpoints d (StarConstants.rho/EpochAlpha.ell k) t ω+6*coreChanges d t ω+
    32*StarOutputMovement.expense d hk t ω+120*wholesaleMass d t ω+
    if t=0 then 480*(k:ℝ) else 0

theorem expense_nonneg (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) :
    0 ≤ expense d hk t ω := by
  have hp := StarOutputMovement.parts_nonneg d hk t ω
  have hn : 0 ≤ if t=0 then 480*(k:ℝ) else 0 := by split_ifs <;> positivity
  unfold expense StarOutputMovement.expense
  linarith [endpoints_nonneg d (StarConstants.rho/EpochAlpha.ell k) t ω,
    core_nonneg d t ω,wholesale_nonneg d t ω,hp.1,hp.2.1,hp.2.2.1,hp.2.2.2]

theorem step (d : Data Ω ι k) (hk : 1 ≤ k) (t : ℕ) (ω : Ω) {q₀ q₁ : ℝ}
    (h₀ : StarLower.parentLower d t ω ≤ q₀) (h₁ : StarLower.parentLower d (t+1) ω ≤ q₁) :
    variation (output d hk t ω q₀) (output d hk (t+1) ω q₁) ≤ |q₁-q₀|+expense d hk t ω := by
  have hm := size_move d hk t ω h₀ h₁
  have hp := StarOutputMovement.parts_nonneg d hk t ω
  have he := endpoints_nonneg d (StarConstants.rho/EpochAlpha.ell k) t ω
  have hc := core_nonneg d t ω
  have hw := wholesale_nonneg d t ω
  have hq := abs_nonneg (q₁-q₀)
  by_cases ht : t=0
  · have hb₀ := held_sum d t ω
    have hb₁ := held_sum d (t+1) ω
    unfold expense StarOutputMovement.expense
    rw [ite_eq_left ht]
    linarith [hp.1,hp.2.1,hp.2.2.1,hp.2.2.2]
  · cases hr : StarCaps.wholesale d t ω
    · have hcap := sum_le_sum (s:=univ) fun i _ => StarCaps.cap_step d hk t ω i hr
      change variation (StarCaps.cap d t ω) (StarCaps.cap d (t+1) ω) ≤ _ at hcap
      simp only [sum_add_distrib,←mul_sum] at hcap
      change _ ≤ 2*endpoints d (StarConstants.rho/EpochAlpha.ell k) t ω+3*coreChanges d t ω at hcap
      have h := StarOutputMovement.rule_move d hk t ω q₀ q₁ h₁ hr
      have ho : output d hk t ω q₀=ruleOutput d hk t ω q₀ := by cases t <;> simp_all [output]
      rw [ho]
      change variation (ruleOutput d hk t ω q₀) (ruleOutput d hk (t+1) ω q₁) ≤ _
      unfold expense
      rw [ite_eq_right ht]
      linarith
    · change _ ≤ |q₁-q₀|+(4*endpoints d (StarConstants.rho/EpochAlpha.ell k) t ω+6*coreChanges d t ω+
        32*StarOutputMovement.expense d hk t ω+120*wholesaleMass d t ω+(if t=0 then 480*(k:ℝ) else 0))
      rw [ite_eq_right ht]
      unfold wholesaleMass StarOutputMovement.expense
      rw [hr]
      simp only [ite_true]
      linarith [hp.1,hp.2.1,hp.2.2.1,hp.2.2.2]

end UniformKServer.StarAllSteps

end


end

end OAI
