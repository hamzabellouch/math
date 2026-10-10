import Mathlib
import OAI.Combinatorics.KMedian.Reduction.DeletionHistory

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

variable (I : Instance)

theorem step_cost {B : ℝ} (hB : 0 ≤ B) (U : Finset (Fin I.n)) :
    cost I (deleteStep I B U) ≤ cost I U+B := by
  classical
  unfold deleteStep
  split_ifs with hk he
  · have hmem := mem_filter.mp (min'_mem (eligible I B U) he)
    have hh := hmem.2
    rw [Rat.cast_sub,I.cast_rationalCost,I.cast_rationalCost] at hh
    linarith only [hh]
  · linarith only [hB]
  · linarith only [hB]

theorem step_budget_lower (B : ℝ) (U : Finset (Fin I.n)) (hU : I.k ≤ U.card) :
    I.k ≤ (deleteStep I B U).card := by
  classical
  unfold deleteStep
  split_ifs with hk he
  · have hi := (mem_filter.mp (min'_mem (eligible I B U) he)).1
    rw [card_erase_of_mem hi]
    omega
  · exact hU
  · exact hU

theorem history_budget_lower (B : ℝ) (T : Finset (Fin I.n)) (hT : I.k ≤ T.card) (t : ℕ) :
    I.k ≤ (deletionHistory I B T t).card := by
  induction t with
  | zero => exact hT
  | succ t ih => exact step_budget_lower I B _ ih

theorem history_cost {B : ℝ} (hB : 0 ≤ B) (T : Finset (Fin I.n)) (t : ℕ) :
    cost I (deletionHistory I B T t) ≤ cost I T+(t:ℝ)*B := by
  induction t with
  | zero => simp only [deletionHistory,Nat.cast_zero,zero_mul,add_zero,le_refl]
  | succ t ih =>
    have hh := step_cost I hB (deletionHistory I B T t)
    change cost I (deletionHistory I B T (t+1)) ≤ _ at hh
    push_cast
    linarith only [ih,hh]

theorem history_fixed (B : ℝ) (T : Finset (Fin I.n))
    (hfix : deleteStep I B T=T) (t : ℕ) : deletionHistory I B T t=T := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [deletionHistory,ih,hfix]

theorem history_succ_left (B : ℝ) (T : Finset (Fin I.n)) (t : ℕ) :
    deletionHistory I B T (t+1)=deletionHistory I B (deleteStep I B T) t := by
  induction t with
  | zero => rfl
  | succ t ih => simpa only [deletionHistory] using congrArg (deleteStep I B) ih

theorem history_endpoint (B : ℝ) (T : Finset (Fin I.n)) (c : ℕ)
    (hT : T.card ≤ I.k+c) :
    let U := deletionHistory I B T c
    U.card ≤ I.k ∨ ∀ i ∈ U, B < cost I (U.erase i)-cost I U := by
  classical
  dsimp only
  induction c generalizing T with
  | zero =>
    left
    simpa only [deletionHistory,Nat.add_zero] using hT
  | succ c ih =>
    by_cases hk : I.k < T.card
    · by_cases he : (eligible I B T).Nonempty
      · let i := (eligible I B T).min' he
        have hi : i ∈ T := (mem_filter.mp (min'_mem _ he)).1
        have hstep : deleteStep I B T=T.erase i := by
          simp only [deleteStep,ite_eq_left hk,dite_eq_left he,i]
        have hcard : (deleteStep I B T).card ≤ I.k+c := by
          rw [hstep,card_erase_of_mem hi]
          omega
        rw [history_succ_left]
        exact ih _ hcard
      · have hfix : deleteStep I B T=T := by simp only [deleteStep,ite_eq_left hk,dite_eq_right he]
        rw [history_fixed I B T hfix (c+1)]
        right
        intro i hi
        have hn : ¬ ((rationalCost I (T.erase i)-rationalCost I T:ℚ):ℝ) ≤ B := by
          intro hh
          exact he ⟨i,mem_filter.mpr ⟨hi,hh⟩⟩
        rw [Rat.cast_sub,I.cast_rationalCost,I.cast_rationalCost] at hn
        exact lt_of_not_ge hn
    · have hfix : deleteStep I B T=T := by simp only [deleteStep,ite_eq_right hk]
      rw [history_fixed I B T hfix (c+1)]
      exact Or.inl (le_of_not_gt hk)

end MetricKMedian.Reduction
end
end

end OAI
