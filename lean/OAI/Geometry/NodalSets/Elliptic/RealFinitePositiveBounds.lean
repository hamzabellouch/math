import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

namespace OAI

namespace Yau

theorem real_finite_positive_majorant {ι : Type*} [Fintype ι] (C : ι → ℝ) :
    ∃ B > 0, ∀ i, C i ≤ B := by
  classical
  refine ⟨(∑ i, |C i|)+1,by linarith [Finset.sum_nonneg (s := Finset.univ) (fun i _ ↦ abs_nonneg (C i))],?_⟩
  intro i
  have hs := Finset.single_le_sum (f := fun j ↦ |C j|) (fun j _ ↦ abs_nonneg (C j)) (Finset.mem_univ i)
  linarith [le_abs_self (C i)]

end Yau

end OAI
