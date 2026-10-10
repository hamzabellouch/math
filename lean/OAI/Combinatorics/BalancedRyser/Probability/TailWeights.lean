import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

namespace OAI

open scoped BigOperators

namespace Balanced
open scoped _root_.Balanced
namespace TailWeights

theorem sum_filter_exists_le {I E : Type*} [DecidableEq I] [DecidableEq E]
    (J : Finset I) (edges : Finset E) (R : I → E → Prop) [DecidableRel R]
    (w : E → ℝ) (hw : ∀ e ∈ edges, 0 ≤ w e) :
    ∑ e ∈ edges.filter (fun e => ∃ i ∈ J, R i e), w e ≤
      ∑ i ∈ J, ∑ e ∈ edges.filter (R i), w e := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro e he
  have he0 : 0 ≤ w e := hw e he
  by_cases h : ∃ i ∈ J, R i e
  · rw [ite_eq_left h]
    obtain ⟨i, hi, hie⟩ := h
    calc
      w e = (if R i e then w e else 0) := by simp [hie]
      _ ≤ ∑ j ∈ J, if R j e then w e else 0 := by
        apply Finset.single_le_sum (f := fun j => if R j e then w e else 0)
        · intro j hj
          split_ifs <;> positivity
        · exact hi
  · simp only [ite_eq_right h]
    apply Finset.sum_nonneg
    intro i hi
    split_ifs <;> positivity

theorem touching_weight_le {I E : Type*} [DecidableEq I] [DecidableEq E]
    (J : Finset I) (edges : Finset E) (R : I → E → Prop) [DecidableRel R]
    (w : E → ℝ) (a : ℝ) (hw : ∀ e ∈ edges, 0 ≤ w e)
    (hslot : ∀ i ∈ J, ∑ e ∈ edges.filter (R i), w e ≤ a) :
    ∑ e ∈ edges.filter (fun e => ∃ i ∈ J, R i e), w e ≤
      (J.card : ℝ) * a := by
  calc
    _ ≤ ∑ i ∈ J, ∑ e ∈ edges.filter (R i), w e :=
      sum_filter_exists_le J edges R w hw
    _ ≤ ∑ _i ∈ J, a := Finset.sum_le_sum hslot
    _ = (J.card : ℝ) * a := by simp

theorem two_slot_weight_le_half {I E : Type*} [DecidableEq I] [DecidableEq E]
    (J : Finset I) (edges : Finset E) (R : I → E → Prop) [DecidableRel R]
    (w : E → ℝ) (hw : ∀ e ∈ edges, 0 ≤ w e)
    (hcard : J.card ≤ 2)
    (hslot : ∀ i ∈ J, ∑ e ∈ edges.filter (R i), w e ≤ 1 / 4) :
    ∑ e ∈ edges.filter (fun e => ∃ i ∈ J, R i e), w e ≤ 1 / 2 := by
  have h := touching_weight_le J edges R w (1 / 4) hw hslot
  have hc : (J.card : ℝ) ≤ 2 := by exact_mod_cast hcard
  linarith

theorem dependency_weight_le_half {I E : Type*} [DecidableEq I] [DecidableEq E]
    (J : Finset I) (edges neighbors : Finset E)
    (R : I → E → Prop) [DecidableRel R] (w : E → ℝ)
    (hw : ∀ e ∈ edges, 0 ≤ w e) (hcard : J.card ≤ 2)
    (hslot : ∀ i ∈ J, ∑ e ∈ edges.filter (R i), w e ≤ 1 / 4)
    (hsub : neighbors ⊆ edges.filter (fun e => ∃ i ∈ J, R i e)) :
    ∑ e ∈ neighbors, w e ≤ 1 / 2 := by
  calc
    _ ≤ ∑ e ∈ edges.filter (fun e => ∃ i ∈ J, R i e), w e := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro e he _
      exact hw e (Finset.mem_filter.mp he).1
    _ ≤ 1 / 2 := two_slot_weight_le_half J edges R w hw hcard hslot

end TailWeights
end Balanced

end OAI
