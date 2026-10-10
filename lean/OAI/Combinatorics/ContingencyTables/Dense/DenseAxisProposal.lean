import OAI.Combinatorics.ContingencyTables.Dense.GridAdjacency

namespace OAI

/-! # Integer signed-coordinate proposals for the dense grid -/

namespace ContingencyTables.GridBoundary

open scoped Classical

variable {I : Type*} [DecidableEq I] {K : ℕ}

/-- A signed step is rejected at the boundary of the declared finite grid. -/
def axisStep (a : Grid (I := I) K) (i : I) (sign : Bool) : Option (Grid (I := I) K) :=
  if sign then
    if h : corner a i + 1 ≤ (K : ℤ) - 1 then
      some (Function.update a i ⟨corner a i + 1, by
        constructor
        · have ha : 0 ≤ corner a i := (a i).property.1; omega
        · exact h⟩)
    else none
  else
    if h : 0 ≤ corner a i - 1 then
      some (Function.update a i ⟨corner a i - 1, by
        constructor
        · exact h
        · have ha : corner a i ≤ (K : ℤ) - 1 := (a i).property.2; omega⟩)
    else none

theorem axisStep_sound (a b : Grid (I := I) K) (i : I) (sign : Bool)
    (h : axisStep a i sign = some b) : OrientedNeighbor a b i sign := by
  cases sign
  · unfold axisStep at h
    simp only [Bool.false_eq_true, ite_false] at h
    split_ifs at h with hc
    · have hb := Option.some.inj h
      rw [← hb]
      change IsGridEdge _
      constructor
      · simp only [corner, Function.update_self]
        omega
      · intro j hj
        change j ≠ i at hj
        simp [Function.update_of_ne hj]
  · unfold axisStep at h
    simp only [ite_true] at h
    split_ifs at h with hc
    · have hb := Option.some.inj h
      rw [← hb]
      change IsGridEdge _
      constructor
      · simp [corner]
      · intro j hj
        change j ≠ i at hj
        simp [Function.update_of_ne hj]

theorem axisStep_complete (a b : Grid (I := I) K) (i : I) (sign : Bool)
    (h : OrientedNeighbor a b i sign) : axisStep a i sign = some b := by
  cases sign
  · change IsGridEdge (b, a, i) at h
    have hc : 0 ≤ corner a i - 1 := by
      have := (b i).property.1
      have he := h.1
      change corner a i = corner b i + 1 at he
      change 0 ≤ corner b i at this
      omega
    unfold axisStep
    simp only [Bool.false_eq_true, ite_false, dite_eq_left hc, Option.some.injEq]
    funext j
    apply Subtype.ext
    by_cases hj : j = i
    · subst j
      simp only [Function.update_self]
      have he := h.1
      change corner a i = corner b i + 1 at he
      change corner a i - 1 = corner b i
      omega
    · simp only [Function.update_of_ne hj]
      exact congrArg Subtype.val (h.2 j hj)
  · change IsGridEdge (a, b, i) at h
    have hc : corner a i + 1 ≤ (K : ℤ) - 1 := by
      have := (b i).property.2
      have he := h.1
      change corner b i = corner a i + 1 at he
      change corner b i ≤ (K : ℤ) - 1 at this
      omega
    unfold axisStep
    simp only [ite_true, dite_eq_left hc, Option.some.injEq]
    funext j
    apply Subtype.ext
    by_cases hj : j = i
    · subst j
      simp only [Function.update_self]
      exact h.1.symm
    · simp only [Function.update_of_ne hj]
      exact congrArg Subtype.val (h.2 j hj).symm

theorem axisStep_some_iff (a b : Grid (I := I) K) (i : I) (sign : Bool) :
    axisStep a i sign = some b ↔ OrientedNeighbor a b i sign :=
  ⟨axisStep_sound a b i sign, axisStep_complete a b i sign⟩

/-- Each neighbouring bin has exactly one signed-coordinate proposal. -/
theorem oriented_direction_unique (a b : Grid (I := I) K) (i j : I) (s t : Bool)
    (hi : OrientedNeighbor a b i s) (hj : OrientedNeighbor a b j t) : (i, s) = (j, t) := by
  have hij : i = j := by
    by_contra hne
    have he : corner a i = corner b i := by
      cases t
      · exact congrArg Subtype.val (hj.2 i hne)
      · exact (congrArg Subtype.val (hj.2 i hne)).symm
    cases s
    · have hp := hi.1
      change corner a i = corner b i + 1 at hp
      omega
    · have hp := hi.1
      change corner b i = corner a i + 1 at hp
      omega
  subst j
  have hst : s = t := by
    cases s <;> cases t
    · rfl
    · have h₁ := hi.1
      have h₂ := hj.1
      change corner a i = corner b i + 1 at h₁
      change corner b i = corner a i + 1 at h₂
      omega
    · have h₁ := hi.1
      have h₂ := hj.1
      change corner b i = corner a i + 1 at h₁
      change corner a i = corner b i + 1 at h₂
      omega
    · rfl
  subst t
  rfl

end ContingencyTables.GridBoundary

end OAI
