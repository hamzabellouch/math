import OAI.NumberTheory.TwoPoint.Bounds.FiniteAverages
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI

/-! Averaging all residue classes combines fixed-progression block estimates. -/

namespace TwoPointCorrelations

open Finset

lemma uniformAverage_swap {α β : Type*} [Fintype α] [Fintype β] (f : α → β → ℝ) :
    uniformAverage (fun x => uniformAverage (f x)) =
      uniformAverage (fun y => uniformAverage (fun x => f x y)) := by
  rw [← uniformAverage_prod, ← uniformAverage_prod]
  exact uniformAverage_equiv (Equiv.prodComm α β) (fun x => f x.2 x.1)

lemma uniformAverage_progression_partition (f : ℕ → ℝ) (l N : ℕ) :
    uniformAverage (fun y : Fin (l * N) => f y.val) =
      uniformAverage (fun b : Fin l => uniformAverage (fun x : Fin N => f (b.val + l * x.val))) := by
  let e : Fin N × Fin l ≃ Fin (l * N) := finProdFinEquiv.trans (finCongr (Nat.mul_comm N l))
  calc
    _ = uniformAverage (fun x : Fin N × Fin l => f (x.2.val + l * x.1.val)) := by
      exact (uniformAverage_equiv e (fun y : Fin (l * N) => f y.val)).symm
    _ = uniformAverage (fun x : Fin N => uniformAverage (fun b : Fin l => f (b.val + l * x.val))) :=
      uniformAverage_prod (fun (x : Fin N) (b : Fin l) => f (b.val + l * x.val))
    _ = _ := uniformAverage_swap _

lemma uniformAverage_le_of_progressions (f : ℕ → ℝ) (l N : ℕ) (hl : 0 < l)
    (C : ℝ) (hf : ∀ b : Fin l, uniformAverage (fun x : Fin N => f (b.val + l * x.val)) ≤ C) :
    uniformAverage (fun y : Fin (l * N) => f y.val) ≤ C := by
  rw [uniformAverage_progression_partition]
  let : Nonempty (Fin l) := ⟨⟨0, hl⟩⟩
  calc
    _ ≤ uniformAverage (fun _ : Fin l => C) := by
      unfold uniformAverage
      exact div_le_div_of_nonneg_right (sum_le_sum (fun b _ => hf b)) (Nat.cast_nonneg _)
    _ = _ := uniformAverage_const _

end TwoPointCorrelations

end OAI
