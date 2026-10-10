import Mathlib

namespace OAI

namespace Problem310.OrderedRouting

/-- The first successful nondefault selector, or the final (default) child. -/
def chooseChild {M : ℕ} (S : Fin M → Bool) : Fin (M + 1) :=
  Fin.find (fun i => Fin.lastCases true S i = true) ⟨Fin.last M, by simp⟩

variable {M : ℕ}

theorem chooseChild_eq_nondefault_iff (S : Fin M → Bool) (i : Fin M) :
    chooseChild S = i.castSucc ↔ S i = true ∧ ∀ j < i, S j = false := by
  rw [chooseChild, Fin.find_eq_iff]
  simp only [Fin.lastCases_castSucc]
  constructor
  · rintro ⟨hi, hmin⟩
    refine ⟨hi, fun j hj => ?_⟩
    have h := hmin j.castSucc (by simpa using hj)
    simpa using h
  · rintro ⟨hi, hmin⟩
    refine ⟨hi, fun j hj => ?_⟩
    induction j using Fin.lastCases with
    | last => exact ((not_lt_of_ge (Fin.le_last _)) hj).elim
    | cast j =>
      have h := hmin j (by simpa using hj)
      simp [h]

theorem chooseChild_eq_default_iff (S : Fin M → Bool) :
    chooseChild S = Fin.last M ↔ ∀ i, S i = false := by
  rw [chooseChild, Fin.find_eq_iff]
  simp only [Fin.lastCases_last, true_and]
  constructor
  · intro h i
    have hi := h i.castSucc (Fin.castSucc_lt_last i)
    simpa using hi
  · intro h j hj
    induction j using Fin.lastCases with
    | last => exact ((lt_irrefl _) hj).elim
    | cast i => simp [h i]

/-- Routing to a nondefault child depends only on selector entries up to it. -/
theorem chooseChild_preserved (S T : Fin M → Bool) (i : Fin M)
    (hS : chooseChild S = i.castSucc) (heq : ∀ j ≤ i, S j = T j) :
    chooseChild T = i.castSucc := by
  obtain ⟨hi, hmin⟩ := (chooseChild_eq_nondefault_iff S i).mp hS
  apply (chooseChild_eq_nondefault_iff T i).mpr
  constructor
  · rw [← heq i le_rfl]
    exact hi
  · intro j hj
    rw [← heq j (le_of_lt hj)]
    exact hmin j hj

/-- Rejected earlier children and a successful current selector determine a hit. -/
theorem chooseChild_of_local_success (S : Fin M → Bool) (i : Fin M)
    (hprev : ∀ j < i, S j = false) (hi : S i = true) :
    chooseChild S = i.castSucc :=
  (chooseChild_eq_nondefault_iff S i).mpr ⟨hi, hprev⟩

/-- Every nondefault child preceding the chosen child was rejected. -/
theorem chooseChild_reject_before (S : Fin M → Bool) (j : Fin M)
    (hj : j.castSucc < chooseChild S) : S j = false := by
  have h := Fin.find_min (p := fun i => Fin.lastCases true S i = true)
    (show ∃ i, Fin.lastCases true S i = true from ⟨Fin.last M, by simp⟩) hj
  simpa using h

/-- A nondefault chosen child has a successful selector. -/
theorem chooseChild_success (S : Fin M → Bool) (i : Fin M)
    (hi : chooseChild S = i.castSucc) : S i = true :=
  ((chooseChild_eq_nondefault_iff S i).mp hi).1

/-- The default is avoided exactly when some nondefault selector succeeds. -/
theorem chooseChild_ne_default_iff (S : Fin M → Bool) :
    chooseChild S ≠ Fin.last M ↔ ∃ i, S i = true := by
  rw [ne_eq, chooseChild_eq_default_iff]
  simp only [not_forall, Bool.not_eq_false]

/-- Pointwise equality of selectors preserves the complete child choice. -/
theorem chooseChild_congr (S T : Fin M → Bool) (h : ∀ i, S i = T i) :
    chooseChild S = chooseChild T := by
  congr 1
  exact funext h

end Problem310.OrderedRouting

end OAI
