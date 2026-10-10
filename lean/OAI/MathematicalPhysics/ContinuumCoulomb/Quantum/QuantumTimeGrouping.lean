import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialInput
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.ChainOfFn

namespace OAI

/-! A literal finite time grouping permutes the interaction list without duplicating terms. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

variable {α : Type*} [DecidableEq α]

def qmaGroupByTime (T : ℕ) (time : α → Fin T) (xs : List α) : List α :=
  (List.ofFn (fun t : Fin T => t)).flatMap (fun t => xs.filter (fun a => decide (time a = t)))

theorem qmaGroupByTime_count (T : ℕ) (time : α → Fin T) (xs : List α) (a : α) :
    (qmaGroupByTime T time xs).count a = xs.count a := by
  have hf (t : Fin T) : (xs.filter (fun b => decide (time b = t))).count a =
      if time a = t then xs.count a else 0 := by
    by_cases h : time a = t
    · simp only [h,ite_true]
      apply List.count_filter
      simp [h]
    · simp only [h,ite_false]
      apply List.count_eq_zero.mpr
      intro ha
      exact h (of_decide_eq_true (List.mem_filter.mp ha).2)
  simp only [qmaGroupByTime,List.count_flatMap,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  simp_rw [hf]
  simp

theorem qmaGroupByTime_perm (T : ℕ) (time : α → Fin T) (xs : List α) :
    (qmaGroupByTime T time xs).Perm xs :=
  List.perm_iff_count.mpr (qmaGroupByTime_count T time xs)

theorem qmaGroupByTime_length (T : ℕ) (time : α → Fin T) (xs : List α) :
    (qmaGroupByTime T time xs).length = xs.length :=
  (qmaGroupByTime_perm T time xs).length_eq

theorem qmaGroupByTime_nodup (T : ℕ) (time : α → Fin T) (xs : List α) (hx : xs.Nodup) :
    (qmaGroupByTime T time xs).Nodup :=
  (qmaGroupByTime_perm T time xs).nodup_iff.mpr hx

omit [DecidableEq α] in
theorem qmaGroupByTime_sorted (T : ℕ) (time : α → Fin T) (xs : List α) :
    (qmaGroupByTime T time xs).Pairwise (fun a b => time a ≤ time b) := by
  unfold qmaGroupByTime
  apply List.pairwise_flatMap.mpr
  constructor
  · intro t _
    apply List.pairwise_of_forall_mem_list
    intro a ha b hb
    have ha' := of_decide_eq_true (List.mem_filter.mp ha).2
    have hb' := of_decide_eq_true (List.mem_filter.mp hb).2
    exact le_of_eq (ha'.trans hb'.symm)
  · apply List.pairwise_ofFn.mpr
    intro i j hij a ha b hb
    have ha' := of_decide_eq_true (List.mem_filter.mp ha).2
    have hb' := of_decide_eq_true (List.mem_filter.mp hb).2
    simpa only [ha',hb'] using le_of_lt hij

end ContinuumCoulomb

end

end OAI
