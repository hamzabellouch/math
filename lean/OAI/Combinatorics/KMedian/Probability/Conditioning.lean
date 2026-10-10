import Mathlib
import OAI.Combinatorics.KMedian.Probability.FiniteLaws

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw
open Finset
variable {Ω : Type*} [Fintype Ω]

noncomputable def condition (μ : FiniteLaw Ω) (P : Ω → Prop) [DecidablePred P]
    (hP : 0 < μ.prob P) : FiniteLaw Ω where
  weight := fun ω => if P ω then μ.weight ω/μ.prob P else 0
  nonneg := fun ω => by split_ifs; exact div_nonneg (μ.nonneg ω) hP.le; exact le_rfl
  total := by
    have he : ∀ ω, (if P ω then μ.weight ω/μ.prob P else 0)=
        (μ.weight ω*(if P ω then 1 else 0))/μ.prob P := by
      intro ω; split_ifs <;> simp
    simp only [he, ← sum_div]
    change μ.prob P/μ.prob P=1
    exact div_self hP.ne'

 theorem condition_support (μ : FiniteLaw Ω) (P : Ω → Prop) [DecidablePred P]
    (hP : 0 < μ.prob P) (ω : Ω) :
    0 < (condition μ P hP).weight ω ↔ P ω ∧ 0 < μ.weight ω := by
  change 0 < (if P ω then μ.weight ω/μ.prob P else 0) ↔ P ω ∧ 0 < μ.weight ω
  split_ifs with hp
  · simp only [hp, true_and]
    exact div_pos_iff_of_pos_right hP
  · simp [hp]

 theorem condition_expect_le (μ : FiniteLaw Ω) (P : Ω → Prop) [DecidablePred P]
    (hP : 0 < μ.prob P) (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    (condition μ P hP).expect f ≤ μ.expect f/μ.prob P := by
  have he : (condition μ P hP).expect f=
      μ.expect (fun ω => if P ω then f ω else 0)/μ.prob P := by
    unfold expect condition
    simp only [sum_div]
    apply sum_congr rfl
    intro ω _
    split_ifs <;> simp [div_mul_eq_mul_div]
  rw [he]
  apply div_le_div_of_nonneg_right _ hP.le
  apply μ.expect_mono
  intro ω
  split_ifs
  · exact le_rfl
  · exact hf ω

 theorem exists_support_le_expect (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    ∃ ω, 0 < μ.weight ω ∧ f ω ≤ μ.expect f := by
  classical
  have hn : ∃ ω, 0 < μ.weight ω := by
    by_contra h
    push Not at h
    have hz : ∀ ω, μ.weight ω=0 := fun ω => le_antisymm (h ω) (μ.nonneg ω)
    have ht := μ.total
    simp only [hz, sum_const_zero] at ht
    norm_num at ht
  by_contra h
  push Not at h
  have hs : μ.expect (fun _ => μ.expect f) < μ.expect f := by
    apply sum_lt_sum
    · intro ω _
      by_cases hp : 0 < μ.weight ω
      · exact mul_le_mul_of_nonneg_left (h ω hp).le (μ.nonneg ω)
      · rw [le_antisymm (le_of_not_gt hp) (μ.nonneg ω), zero_mul, zero_mul]
    · obtain ⟨ω,hω⟩ := hn
      exact ⟨ω, mem_univ _, mul_lt_mul_of_pos_left (h ω hω) hω⟩
  rw [expect_const] at hs
  exact lt_irrefl _ hs

theorem select_success (μ : FiniteLaw Ω) (P : Ω → Prop) [DecidablePred P]
    (hP : 0 < μ.prob P) (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    ∃ ω, 0 < μ.weight ω ∧ P ω ∧ f ω ≤ μ.expect f/μ.prob P := by
  obtain ⟨ω,hω,hfω⟩ := (condition μ P hP).exists_support_le_expect f
  obtain ⟨hp,hw⟩ := (condition_support μ P hP ω).mp hω
  exact ⟨ω,hw,hp,hfω.trans (condition_expect_le μ P hP f hf)⟩

 theorem select_success_bound (μ : FiniteLaw Ω) (P : Ω → Prop) [DecidablePred P]
    (f : Ω → ℝ) {p C : ℝ} (hp : 0 < p) (hP : p ≤ μ.prob P)
    (hf : ∀ ω, 0 ≤ f ω) (hE : μ.expect f ≤ C) :
    ∃ ω, 0 < μ.weight ω ∧ P ω ∧ f ω ≤ C/p := by
  obtain ⟨ω,hw,hgood,hcost⟩ := select_success μ P (hp.trans_le hP) f hf
  refine ⟨ω,hw,hgood,hcost.trans ?_⟩
  exact (div_le_div_of_nonneg_right hE (prob_nonneg μ P)).trans
    (div_le_div_of_nonneg_left ((μ.expect_nonneg hf).trans hE) hp hP)

end MetricKMedian.FiniteLaw
end
end

end OAI
