import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Probability.IndependentTrials

namespace OAI

open MeasureTheory

namespace Balanced.IndependentTrials

variable {T : ℕ} {A : Fin T → Type*}

def reassembleAt (i : Fin T)
    (x : ∀ j : {j : Fin T // j.val < i.val}, A j)
    (z : A i) (v : ∀ j : {j : Fin T // i.val < j.val}, A j) : ∀ j, A j :=
  fun j => if h : j.val < i.val then x ⟨j, h⟩ else
    if e : j = i then e.symm ▸ z else v ⟨j, by omega⟩

theorem reassembleAt_restrict (i : Fin T) (w : ∀ j, A j) :
    reassembleAt i (fun j => w j) (w i) (fun j => w j) = w := by
  funext j
  by_cases h : j.val < i.val
  · simp [reassembleAt, h]
  · by_cases e : j = i
    · subst j
      simp [reassembleAt]
    · simp [reassembleAt, h, e]

theorem reassembleAt_eq_of_ne (i : Fin T)
    (x : ∀ j : {j : Fin T // j.val < i.val}, A j)
    (z z' : A i) (v : ∀ j : {j : Fin T // i.val < j.val}, A j)
    (j : Fin T) (hji : j ≠ i) :
    reassembleAt i x z v j = reassembleAt i x z' v j := by
  unfold reassembleAt
  split_ifs <;> rfl

variable [∀ j, MeasurableSpace (A j)]

theorem measurable_reassembleAt (i : Fin T) :
    Measurable (fun p : ((∀ j : {j : Fin T // j.val < i.val}, A j) × A i) ×
        (∀ j : {j : Fin T // i.val < j.val}, A j) =>
      reassembleAt i p.1.1 p.1.2 p.2) := by
  apply Measurable.of_eval
  intro j
  by_cases h : j.val < i.val
  · simpa only [reassembleAt, dite_eq_left h, Function.comp_def] using
      (measurable_pi_apply (⟨j, h⟩ : {j : Fin T // j.val < i.val})).comp (measurable_fst.comp measurable_fst)
  · by_cases e : j = i
    · subst j
      simpa [reassembleAt, Function.comp_def] using
        (measurable_snd.comp measurable_fst)
    · simpa only [reassembleAt, dite_eq_right h, dite_eq_right e, Function.comp_def] using
        (measurable_pi_apply (⟨j, by omega⟩ : {j : Fin T // i.val < j.val})).comp measurable_snd

end Balanced.IndependentTrials

end OAI
