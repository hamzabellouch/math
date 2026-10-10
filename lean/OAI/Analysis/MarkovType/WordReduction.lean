import OAI.Analysis.MarkovType.FourLetters
import Mathlib.Data.List.Chain
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

namespace OAI

namespace MarkovSuperreflexivity

open scoped BigOperators

def step (s : Letter) : List Letter → List Letter
  | [] => [s]
  | a :: r => if s = a.inv then r else s :: a :: r

def scanWord (w r : List Letter) : List Letter :=
  w.foldl (fun stack s => step s stack) r

def reduceWord (w : List Letter) : List Letter := (scanWord w []).reverse

def reducedLength (w : List Letter) : ℕ := (reduceWord w).length

def ReducedWord (w : List Letter) : Prop :=
  List.IsChain (fun a b => b ≠ a.inv) w

@[simp] theorem step_nil (s : Letter) : step s [] = [s] := rfl

@[simp] theorem step_cancel (a : Letter) (r : List Letter) :
    step a.inv (a :: r) = r := by simp [step]

theorem step_keep {s a : Letter} (r : List Letter) (h : s ≠ a.inv) :
    step s (a :: r) = s :: a :: r := by simp [step, h]

@[simp] theorem scanWord_nil (r : List Letter) : scanWord [] r = r := rfl

theorem scanWord_cons (s : Letter) (w r : List Letter) :
    scanWord (s :: w) r = scanWord w (step s r) := rfl

theorem scanWord_append (u v r : List Letter) :
    scanWord (u ++ v) r = scanWord v (scanWord u r) := by
  simp only [scanWord, List.foldl_append]

theorem scanWord_append_singleton (w : List Letter) (s : Letter) :
    scanWord (w ++ [s]) [] = step s (scanWord w []) := by
  rw [scanWord_append, scanWord_cons, scanWord_nil]

@[simp] theorem reduceWord_nil : reduceWord [] = [] := rfl

theorem reduceWord_append_singleton (w : List Letter) (s : Letter) :
    reduceWord (w ++ [s]) = (step s (reduceWord w).reverse).reverse := by
  simp only [reduceWord, scanWord_append_singleton, List.reverse_reverse]

@[simp] theorem reducedWord_nil : ReducedWord [] := List.isChain_nil

@[simp] theorem reducedWord_singleton (s : Letter) : ReducedWord [s] :=
  List.isChain_singleton s

theorem reducedWord_cons (s a : Letter) (w : List Letter) :
    ReducedWord (s :: a :: w) ↔ a ≠ s.inv ∧ ReducedWord (a :: w) :=
  List.isChain_cons_cons

theorem ReducedWord.tail {w : List Letter} (h : ReducedWord w) :
    ReducedWord w.tail := List.IsChain.tail h

theorem ReducedWord.take {w : List Letter} (h : ReducedWord w) (i : ℕ) :
    ReducedWord (w.take i) := List.IsChain.take h i

theorem ReducedWord.drop {w : List Letter} (h : ReducedWord w) (i : ℕ) :
    ReducedWord (w.drop i) := List.IsChain.drop h i

theorem ReducedWord.reverse {w : List Letter} (h : ReducedWord w) :
    ReducedWord w.reverse := by
  apply List.isChain_reverse.mpr
  exact List.IsChain.imp (fun {a b} hab hba => hab ((Letter.eq_inv_iff a b).mp hba)) h

theorem reducedWord_append (u v : List Letter) :
    ReducedWord (u ++ v) ↔ ReducedWord u ∧ ReducedWord v ∧
      ∀ a ∈ u.getLast?, ∀ b ∈ v.head?, b ≠ a.inv :=
  List.isChain_append

theorem ReducedWord.append {u v : List Letter}
    (hu : ReducedWord u) (hv : ReducedWord v)
    (h : ∀ a ∈ u.getLast?, ∀ b ∈ v.head?, b ≠ a.inv) :
    ReducedWord (u ++ v) := List.IsChain.append hu hv h

theorem ReducedWord.step {r : List Letter} (h : ReducedWord r) (s : Letter) :
    ReducedWord (step s r) := by
  cases r with
  | nil => exact reducedWord_singleton s
  | cons a r =>
    by_cases hs : s = a.inv
    · rw [hs, MarkovSuperreflexivity.step_cancel]
      exact h.tail
    · rw [step_keep r hs]
      apply (reducedWord_cons s a r).mpr
      refine ⟨?_, h⟩
      intro ha
      exact hs ((Letter.eq_inv_iff a s).mp ha)

theorem reducedWord_scan {r : List Letter} (h : ReducedWord r) (w : List Letter) :
    ReducedWord (scanWord w r) := by
  induction w generalizing r with
  | nil => exact h
  | cons s w ih =>
    rw [scanWord_cons]
    exact ih (h.step s)

theorem reducedWord_reduceWord (w : List Letter) : ReducedWord (reduceWord w) :=
  (reducedWord_scan reducedWord_nil w).reverse

theorem reduceWord_reduced (w : List Letter) : ReducedWord (reduceWord w) :=
  reducedWord_reduceWord w

inductive CancelPair : List Letter → List Letter → Prop
  | erase (u v : List Letter) (s : Letter) :
      CancelPair (u ++ s :: s.inv :: v) (u ++ v)

abbrev WordReduction : List Letter → List Letter → Prop :=
  Relation.ReflTransGen CancelPair

theorem scanWord_reachable (w r : List Letter) :
    WordReduction (r.reverse ++ w) (scanWord w r).reverse := by
  induction w generalizing r with
  | nil =>
    simpa only [scanWord_nil, List.append_nil] using
      (Relation.ReflTransGen.refl : WordReduction r.reverse r.reverse)
  | cons s w ih =>
    rw [scanWord_cons]
    cases r with
    | nil =>
      simpa only [step_nil, List.reverse_nil, List.nil_append,
        List.reverse_singleton, List.singleton_append] using ih [s]
    | cons a r =>
      by_cases hs : s = a.inv
      · subst s
        rw [step_cancel]
        have hdel : CancelPair ((a :: r).reverse ++ a.inv :: w) (r.reverse ++ w) := by
          simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
            CancelPair.erase r.reverse w a
        exact (ih r).head hdel
      · rw [step_keep r hs]
        simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
          List.cons_append, List.nil_append] using ih (s :: a :: r)

theorem reduceWord_red (w : List Letter) : WordReduction w (reduceWord w) := by
  simpa only [List.reverse_nil, List.nil_append, reduceWord] using scanWord_reachable w []

theorem ReducedWord.no_cancel {w : List Letter} (h : ReducedWord w) :
    ∀ v, ¬ CancelPair w v := by
  intro v hdel
  cases hdel with
  | erase u v s =>
    exact (List.isChain_append_cons_cons.mp h).2.1 rfl

theorem ReducedWord.eq_of_reduction {w v : List Letter}
    (h : ReducedWord w) (hred : WordReduction w v) : w = v :=
  ((Relation.reflTransGen_iff_eq h.no_cancel).mp hred).symm

theorem reduceWord_of_reduced {w : List Letter} (h : ReducedWord w) :
    reduceWord w = w := (h.eq_of_reduction (reduceWord_red w)).symm

@[simp] theorem reduceWord_idem (w : List Letter) :
    reduceWord (reduceWord w) = reduceWord w :=
  reduceWord_of_reduced (reducedWord_reduceWord w)

theorem wordReduction_invariant {α : Sort*} {F : List Letter → α}
    (hcancel : ∀ u s v, F (u ++ s :: s.inv :: v) = F (u ++ v))
    {u v : List Letter} (h : WordReduction u v) : F u = F v := by
  induction h with
  | refl => rfl
  | tail hred hdel ih =>
    cases hdel with
    | erase a b s => exact ih.trans (hcancel a s b)

theorem reduceWord_invariant {α : Sort*} {F : List Letter → α}
    (hcancel : ∀ u s v, F (u ++ s :: s.inv :: v) = F (u ++ v))
    (w : List Letter) : F (reduceWord w) = F w :=
  (wordReduction_invariant hcancel (reduceWord_red w)).symm

theorem step_length_cons (s a : Letter) (r : List Letter) :
    (step s (a :: r)).length = if s = a.inv then r.length else r.length + 2 := by
  by_cases h : s = a.inv <;> simp [step, h, Nat.add_assoc]

theorem step_length_le (s : Letter) (r : List Letter) :
    (step s r).length ≤ r.length + 1 := by
  cases r with
  | nil => simp [step]
  | cons a r =>
    by_cases h : s = a.inv <;> simp [step, h] ; omega

theorem step_cancels_iff (s a : Letter) (r : List Letter) :
    (step s (a :: r)).length = (a :: r).length - 1 ↔ s = a.inv := by
  by_cases h : s = a.inv <;> simp [step, h] ; omega

theorem sum_step_length (r : List Letter) :
    (∑ s : Letter, (step s r).length) =
      4 * r.length + (if r = [] then 4 else 2) := by
  cases r with
  | nil => simp [step]
  | cons a r =>
    rcases a with ⟨a, b⟩
    fin_cases a <;> cases b <;>
      simp [step, Letter.inv, Fintype.sum_prod_type, Fin.sum_univ_two
        ] <;> omega

theorem scanWord_length_le (w r : List Letter) :
    (scanWord w r).length ≤ r.length + w.length := by
  induction w generalizing r with
  | nil => simp only [scanWord_nil, List.length_nil, Nat.add_zero, le_refl]
  | cons s w ih =>
    rw [scanWord_cons, List.length_cons]
    have hi := ih (step s r)
    have hs := step_length_le s r
    omega

@[simp] theorem reducedLength_nil : reducedLength [] = 0 := rfl

theorem reducedLength_le (w : List Letter) : reducedLength w ≤ w.length := by
  simpa only [reducedLength, reduceWord, List.length_reverse, List.length_nil,
    Nat.zero_add] using scanWord_length_le w []

theorem sum_reducedLength_append (w : List Letter) :
    (∑ s : Letter, reducedLength (w ++ [s])) =
      4 * reducedLength w + (if reducedLength w = 0 then 4 else 2) := by
  simpa only [reducedLength, reduceWord, List.length_reverse,
    scanWord_append_singleton, List.length_eq_zero_iff] using sum_step_length (scanWord w [])

theorem sum_reducedLength_append_ge (w : List Letter) :
    4 * reducedLength w + 2 ≤ ∑ s : Letter, reducedLength (w ++ [s]) := by
  rw [sum_reducedLength_append]
  split_ifs <;> omega

end MarkovSuperreflexivity

end OAI
