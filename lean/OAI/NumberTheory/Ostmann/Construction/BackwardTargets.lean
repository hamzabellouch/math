import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

/-! # The backwards pivot-target recurrence

For coefficients `c_j = 2^j J + a_j - Delta_j`, the pivot target is `c_j`
plus the sum of all later pivot targets. This constructs the recurrence,
rather than assuming that its simultaneous equations have a solution.
-/

namespace Ostmann

def backwardTargets : List ℝ → List ℝ
  | [] => []
  | c :: cs => let ts := backwardTargets cs; (c + ts.sum) :: ts

theorem backwardTargets_length (cs : List ℝ) : (backwardTargets cs).length = cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [backwardTargets, List.length_cons, ih]

theorem backwardTargets_sum_cons (c : ℝ) (cs : List ℝ) :
    (backwardTargets (c :: cs)).sum = c + 2 * (backwardTargets cs).sum := by
  simp only [backwardTargets, List.sum_cons]
  ring

theorem backwardTargets_drop (cs : List ℝ) (n : ℕ) :
    (backwardTargets cs).drop n = backwardTargets (cs.drop n) := by
  induction n generalizing cs with
  | zero => simp
  | succ n ih =>
    cases cs with
    | nil => simp [backwardTargets]
    | cons c cs => simpa only [backwardTargets, List.drop_succ_cons] using ih cs

theorem backwardTargets_get (cs : List ℝ) (i : ℕ) (hi : i < cs.length) :
    (backwardTargets cs)[i]'(by rw [backwardTargets_length]; exact hi) =
      cs[i] + ((backwardTargets cs).drop (i + 1)).sum := by
  induction cs generalizing i with
  | nil => simp at hi
  | cons c cs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simpa only [backwardTargets, List.getElem_cons_succ, List.drop_succ_cons] using
        ih i (by simpa using hi)

theorem backwardTargets_nonneg (cs : List ℝ) (hcs : ∀ c ∈ cs, 0 ≤ c) :
    ∀ t ∈ backwardTargets cs, 0 ≤ t := by
  induction cs with
  | nil => simp [backwardTargets]
  | cons c cs ih =>
    have hc : 0 ≤ c := hcs c (by simp)
    have htail : ∀ x ∈ cs, 0 ≤ x := fun x hx => hcs x (by simp [hx])
    intro t ht
    simp only [backwardTargets, List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact add_nonneg hc (List.sum_nonneg (ih htail))
    · exact ih htail t ht

theorem backwardTargets_sum_upper (cs : List ℝ) (C : ℝ)
    (hcs : ∀ c ∈ cs, c ≤ C) :
    (backwardTargets cs).sum ≤ C * ((2 : ℝ) ^ cs.length - 1) := by
  induction cs with
  | nil => simp [backwardTargets]
  | cons c cs ih =>
    have hc := hcs c (by simp)
    have ht := ih (fun x hx => hcs x (by simp [hx]))
    rw [backwardTargets_sum_cons, List.length_cons, pow_succ]
    linarith

/-- Every target is at least the final coefficient when the coefficients
are nonnegative. Thus the last pivot controls the common lower scale. -/
theorem backwardTargets_lower_last (cs : List ℝ) (hne : cs ≠ [])
    (hcs : ∀ c ∈ cs, 0 ≤ c) :
    ∀ t ∈ backwardTargets cs, cs.getLast hne ≤ t := by
  induction cs with
  | nil => exact False.elim (hne rfl)
  | cons c cs ih =>
    cases cs with
    | nil => simp [backwardTargets]
    | cons d ds =>
      have htail : ∀ x ∈ d :: ds, 0 ≤ x := fun x hx => hcs x (by simp [hx])
      have hlast := ih (by simp) htail
      have hnonneg := backwardTargets_nonneg (d :: ds) htail
      have hhead : d + (backwardTargets ds).sum ∈ backwardTargets (d :: ds) := by
        simp [backwardTargets]
      have hsum := List.single_le_sum hnonneg _ hhead
      have hlow := hlast _ hhead
      intro t ht
      change t ∈ (c + (backwardTargets (d :: ds)).sum) :: backwardTargets (d :: ds) at ht
      rcases List.mem_cons.mp ht with rfl | ht
      · have hc := hcs c (by simp)
        simpa only [List.getLast_cons_cons] using hlow.trans (by linarith :
          d + (backwardTargets ds).sum ≤ c + (backwardTargets (d :: ds)).sum)
      · simpa only [List.getLast_cons_cons] using hlast t ht

theorem backwardTargets_each_upper (cs : List ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hcs : ∀ c ∈ cs, 0 ≤ c ∧ c ≤ C) :
    ∀ t ∈ backwardTargets cs, t ≤ C * (2 : ℝ) ^ cs.length := by
  intro t ht
  have hsum := backwardTargets_sum_upper cs C (fun c hc => (hcs c hc).2)
  have hsingle := List.single_le_sum (backwardTargets_nonneg cs (fun c hc => (hcs c hc).1)) t ht
  linarith

end Ostmann

end OAI
