import Mathlib

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {E : Type} [DecidableEq E]

theorem retain_count (F : Finset E) (q : E → ℕ) {k : ℕ} (hk : k ≤ ∑ e ∈ F, q e) :
    ∃ r : E → ℕ, (∀ e, r e ≤ q e) ∧ (∀ e, e ∉ F → r e=0) ∧ (∑ e ∈ F, r e)=k := by
  induction F using Finset.induction_on generalizing k with
  | empty =>
    have hk0 : k=0 := by simpa only [sum_empty,Nat.le_zero] using hk
    exact ⟨fun _ => 0,fun e => Nat.zero_le _,fun _ _ => rfl,by simp only [sum_empty,hk0]⟩
  | @insert e F he ih =>
    rw [sum_insert he] at hk
    let a := min (q e) k
    have ha : a ≤ q e := min_le_left _ _
    have hak : a ≤ k := min_le_right _ _
    have hr : k-a ≤ ∑ f ∈ F, q f := by dsimp only [a]; omega
    obtain ⟨r,hrq,hr0,hrsum⟩ := ih hr
    refine ⟨Function.update r e a,?_,?_,?_⟩
    · intro f
      by_cases hf : f=e
      · subst f; simpa only [Function.update_self] using ha
      · simpa only [Function.update_of_ne hf] using hrq f
    · intro f hf
      have hfe : f ≠ e := fun h => hf (h ▸ mem_insert_self e F)
      have hfF : f ∉ F := fun h => hf (mem_insert_of_mem h)
      rw [Function.update_of_ne hfe,hr0 f hfF]
    · rw [sum_insert he,Function.update_self]
      have heq : (∑ f ∈ F, Function.update r e a f)=∑ f ∈ F, r f := by
        apply sum_congr rfl
        intro f hf
        have hfe : f ≠ e := by
          intro h
          subst f
          exact he hf
        exact Function.update_of_ne hfe a r
      rw [heq,hrsum]
      omega

theorem retained_table [Fintype E] {T Ω : Type} (q : Ω → T → E → ℕ) (Δ : ℕ) :
    ∃ r : Ω → T → E → ℕ,
      (∀ ω t e, r ω t e ≤ q ω t e) ∧
      (∀ ω t, (∑ e, r ω t e)=min (∑ e, q ω t e) (Δ/2)) := by
  classical
  choose r hr hzero hsum using fun ω t => retain_count univ (q ω t)
    (min_le_left (∑ e, q ω t e) (Δ/2))
  exact ⟨r,hr,hsum⟩

end MetricKMedian.Preparation
end
end

end OAI
