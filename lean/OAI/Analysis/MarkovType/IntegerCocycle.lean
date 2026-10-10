import OAI.Analysis.MarkovType.WordAction
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

noncomputable section

def arcIndicator (s : Letter) (y : ℝ) : ℤ := by
  classical
  exact if y ∈ arc s then 1 else 0

def negativeIndicator (s : Letter) : ℤ := if s.2 then 0 else 1

def chi (s : Letter) (y : ℝ) : ℤ := arcIndicator s y - negativeIndicator s

theorem chi_of_mem (s : Letter) (y : ℝ) (hy : y ∈ arc s) :
    chi s y = 1 - negativeIndicator s := by
  simp only [chi, arcIndicator, ite_eq_left hy]

theorem chi_of_not_mem (s : Letter) (y : ℝ) (hy : y ∉ arc s) :
    chi s y = -negativeIndicator s := by
  simp only [chi, arcIndicator, ite_eq_right hy, zero_sub]

theorem negativeIndicator_inv (s : Letter) :
    negativeIndicator s.inv = 1 - negativeIndicator s := by
  rcases s with ⟨i, b⟩
  cases b <;> rfl

theorem arcIndicator_inv_symm (s : Letter) (y : ℝ) :
    arcIndicator s.inv ((letterOrderIso s).symm y) = 1 - arcIndicator s y := by
  by_cases hy : y ∈ arc s
  · have hnot : (letterOrderIso s).symm y ∉ arc s.inv := by
      intro hmem
      exact (symm_mem_inv_arc_iff s y).mp hmem hy
    simp only [arcIndicator, ite_eq_right hnot, ite_eq_left hy, sub_self]
  · have hmem : (letterOrderIso s).symm y ∈ arc s.inv :=
      (symm_mem_inv_arc_iff s y).mpr hy
    simp only [arcIndicator, ite_eq_left hmem, ite_eq_right hy, sub_zero]

theorem chi_inv_symm (s : Letter) (y : ℝ) :
    chi s.inv ((letterOrderIso s).symm y) = -chi s y := by
  simp only [chi, arcIndicator_inv_symm, negativeIndicator_inv]
  ring

theorem chi_add_int (s : Letter) (y : ℝ) (j : ℤ) :
    chi s (y + (j : ℝ)) = chi s y := by
  by_cases hy : y ∈ arc s
  · have hy' : y + (j : ℝ) ∈ arc s := (mem_arc_add_int_iff s y j).mpr hy
    simp only [chi, arcIndicator, ite_eq_left hy, ite_eq_left hy']
  · have hy' : y + (j : ℝ) ∉ arc s := by
      intro h
      exact hy ((mem_arc_add_int_iff s y j).mp h)
    simp only [chi, arcIndicator, ite_eq_right hy, ite_eq_right hy']

def wordCocycle : List Letter → ℝ → ℤ
  | [], _ => 0
  | s :: w, y => chi s y + wordCocycle w ((letterOrderIso s).symm y)

@[simp] theorem wordCocycle_nil (y : ℝ) : wordCocycle [] y = 0 := rfl

@[simp] theorem wordCocycle_cons (s : Letter) (w : List Letter) (y : ℝ) :
    wordCocycle (s :: w) y =
      chi s y + wordCocycle w ((letterOrderIso s).symm y) := rfl

theorem wordCocycle_append (u v : List Letter) (y : ℝ) :
    wordCocycle (u ++ v) y =
      wordCocycle u y + wordCocycle v ((wordMap u).symm y) := by
  induction u generalizing y with
  | nil => simp
  | cons s u ih =>
      simp only [List.cons_append, wordCocycle_cons, wordMap_cons_symm, ih]
      ring

theorem wordCocycle_cancel (u : List Letter) (s : Letter) (v : List Letter)
    (y : ℝ) :
    wordCocycle (u ++ s :: s.inv :: v) y = wordCocycle (u ++ v) y := by
  have hlocal (x : ℝ) : wordCocycle (s :: s.inv :: v) x = wordCocycle v x := by
    simp only [wordCocycle_cons, chi_inv_symm, letterOrderIso_inv,
      OrderIso.symm_symm, OrderIso.apply_symm_apply]
    ring
  rw [wordCocycle_append, wordCocycle_append, hlocal]

theorem wordCocycle_reduceWord (w : List Letter) (y : ℝ) :
    wordCocycle (reduceWord w) y = wordCocycle w y :=
  reduceWord_invariant (F := fun v => wordCocycle v y)
    (fun u s v => wordCocycle_cancel u s v y) w

private theorem letter_symm_add_int (s : Letter) (y : ℝ) (j : ℤ) :
    (letterOrderIso s).symm (y + (j : ℝ)) =
      (letterOrderIso s).symm y + (j : ℝ) := by
  apply (letterOrderIso s).injective
  rw [OrderIso.apply_symm_apply, letterOrderIso_add_int, OrderIso.apply_symm_apply]

theorem wordCocycle_add_int (w : List Letter) (y : ℝ) (j : ℤ) :
    wordCocycle w (y + (j : ℝ)) = wordCocycle w y := by
  induction w generalizing y with
  | nil => rfl
  | cons s w ih =>
      simp only [wordCocycle_cons, chi_add_int, letter_symm_add_int, ih]

theorem wordCocycle_inverseWord (w : List Letter) (y : ℝ) :
    wordCocycle (inverseWord w) ((wordMap w).symm y) = -wordCocycle w y := by
  induction w generalizing y with
  | nil => simp
  | cons s w ih =>
      simp only [inverseWord_cons, wordCocycle_append, wordMap_cons_symm,
        ih, wordMap_inverseWord, OrderIso.symm_symm, OrderIso.apply_symm_apply,
        wordCocycle_cons, wordCocycle_nil, add_zero, chi_inv_symm]
      ring

def pullbackPoint (w : List Letter) (k : ℕ) (y : ℝ) : ℝ :=
  (wordMap (w.take k)).symm y

@[simp] theorem pullbackPoint_zero (w : List Letter) (y : ℝ) :
    pullbackPoint w 0 y = y := rfl

@[simp] theorem pullbackPoint_nil (k : ℕ) (y : ℝ) :
    pullbackPoint [] k y = y := by
  simp only [pullbackPoint, List.take_nil, wordMap_nil_symm]

theorem pullbackPoint_cons_succ (s : Letter) (w : List Letter) (k : ℕ) (y : ℝ) :
    pullbackPoint (s :: w) (k + 1) y =
      pullbackPoint w k ((letterOrderIso s).symm y) := by
  simp only [pullbackPoint, List.take_succ_cons, wordMap_cons_symm]

theorem pullbackPoint_succ (w : List Letter) {i : ℕ} (hi : i < w.length) (y : ℝ) :
    pullbackPoint w (i + 1) y =
      (letterOrderIso (w.get ⟨i, hi⟩)).symm (pullbackPoint w i y) := by
  induction w generalizing i y with
  | nil => simp only [List.length_nil] at hi; omega
  | cons s w ih =>
      cases i with
      | zero => simp [pullbackPoint]
      | succ i =>
          have hi' : i < w.length := Nat.lt_of_succ_lt_succ hi
          simpa only [pullbackPoint_cons_succ, List.get_eq_getElem,
            List.getElem_cons_succ] using
            ih hi' ((letterOrderIso s).symm y)

theorem letterOrderIso_pullbackPoint_succ (w : List Letter) (i : Fin w.length)
    (y : ℝ) :
    letterOrderIso (w.get i) (pullbackPoint w (i.val + 1) y) =
      pullbackPoint w i.val y := by
  rw [pullbackPoint_succ w i.isLt, OrderIso.apply_symm_apply]

theorem pullbackPoint_wordMap (w : List Letter) (i : ℕ) (y : ℝ) :
    pullbackPoint w i (wordMap w y) = wordMap (w.drop i) y :=
  prefixState_wordMap w i y

theorem pullbackPoint_add_int (w : List Letter) (i : ℕ) (y : ℝ) (j : ℤ) :
    pullbackPoint w i (y + (j : ℝ)) = pullbackPoint w i y + (j : ℝ) :=
  wordMap_symm_add_int (w.take i) y j

theorem pullbackPoint_int (w : List Letter) (i : ℕ) (j : ℤ) :
    pullbackPoint w i (j : ℝ) =
      wordMap (inverseWord (w.take i)) 0 + (j : ℝ) :=
  prefixState_int w i j

theorem pullbackPoint_wordMap_add_int (w : List Letter) (i : ℕ) (y : ℝ) (j : ℤ) :
    pullbackPoint w i (wordMap w y + (j : ℝ)) =
      wordMap (w.drop i) y + (j : ℝ) :=
  prefixState_wordMap_add_int w i y j

theorem wordCocycle_eq_sum (w : List Letter) (y : ℝ) :
    wordCocycle w y =
      ∑ i : Fin w.length, chi (w.get i) (pullbackPoint w i.val y) := by
  induction w generalizing y with
  | nil => simp
  | cons s w ih =>
      change chi s y + wordCocycle w ((letterOrderIso s).symm y) =
        ∑ i : Fin (w.length + 1), chi ((s :: w).get i) (pullbackPoint (s :: w) i.val y)
      rw [ih, Fin.sum_univ_succ]
      simp only [List.get_eq_getElem, List.getElem_cons_zero, List.getElem_cons_succ,
        Fin.val_zero, Fin.val_succ, pullbackPoint_zero, pullbackPoint_cons_succ]

end

end MarkovSuperreflexivity

end OAI
