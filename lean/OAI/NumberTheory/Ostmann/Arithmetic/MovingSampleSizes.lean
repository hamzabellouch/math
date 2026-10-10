import OAI.NumberTheory.Ostmann.Arithmetic.MovingSampleSlots

namespace OAI

/-! # Concrete degree budgets for the sampled moving-giant paths -/

namespace Ostmann

def MovingLeafLengthLE {σ : Type*} : (n : ℕ) → TreeLeafTuple (List σ) n → ℕ → Prop
  | 0, x, A => (show List σ from x).length ≤ A
  | n + 1, x, A => MovingLeafLengthLE n x.1 A ∧ MovingLeafLengthLE n x.2 A

theorem moving_flatten_length_le {σ : Type*} (n : ℕ) (x : TreeLeafTuple (List σ) n)
    (A : ℕ) (hx : MovingLeafLengthLE n x A) :
    (flattenMovingSlots n x).length ≤ 2 ^ n * A := by
  induction n with
  | zero => simpa only [MovingLeafLengthLE, flattenMovingSlots, pow_zero, one_mul] using hx
  | succ n ih =>
    simp only [flattenMovingSlots, List.length_append]
    have h := Nat.add_le_add (ih x.1 hx.1) (ih x.2 hx.2)
    convert h using 1
    rw [pow_succ]
    ring

theorem moving_append_length_le {σ : Type*} (n : ℕ)
    (x y : TreeLeafTuple (List σ) n) (A B : ℕ)
    (hx : MovingLeafLengthLE n x A) (hy : MovingLeafLengthLE n y B) :
    MovingLeafLengthLE n (appendMovingSlotLeaves n x y) (A + B) := by
  induction n with
  | zero =>
    change ((show List σ from x) ++ (show List σ from y)).length ≤ A + B
    rw [List.length_append]
    exact Nat.add_le_add hx hy
  | succ n ih => exact ⟨ih x.1 y.1 hx.1 hy.1, ih x.2 y.2 hx.2 hy.2⟩

theorem moving_compensation_length {σ : Type*} (n : ℕ)
    (samples : TreeLeafTuple (Fin 4 → σ) n) :
    MovingLeafLengthLE n (movingCompensationSlots n samples) 4 := by
  induction n with
  | zero => simp [MovingLeafLengthLE, movingCompensationSlots]
  | succ n ih => exact ⟨ih samples.1, ih samples.2⟩

def MovingSlotData.SizeLE {σ : Type*} (D : ℕ) : {n : ℕ} → MovingSlotData σ n → Prop
  | _, .leaf _ _ => True
  | _, .node _ CL CR u left right =>
      CL.length ≤ D ∧ CR.length ≤ D ∧ u.length ≤ D ∧ left.SizeLE D ∧ right.SizeLE D

theorem MovingSlotData.SizeLE.mono {σ : Type*} {n D E : ℕ} {T : MovingSlotData σ n}
    (h : T.SizeLE D) (hDE : D ≤ E) : T.SizeLE E := by
  induction T with
  | leaf => trivial
  | node s CL CR u left right ihL ihR =>
    exact ⟨h.1.trans hDE, h.2.1.trans hDE, h.2.2.1.trans hDE, ihL h.2.2.2.1, ihR h.2.2.2.2⟩

/-- Compensation adds exactly four labels per bottom leaf per level. -/
theorem buildMovingSlotData_size {σ : Type*} (n : ℕ) (t : FrequencyTree ℤ n)
    (small bulk : TreeLeafTuple (List σ) n) (samples : MovingSampleSlots σ n)
    (A B : ℕ) (hsmall : MovingLeafLengthLE n small A) (hbulk : MovingLeafLengthLE n bulk B) :
    (buildMovingSlotData n t small bulk samples).SizeLE (2 ^ n * (A + B + 4 * n + 4)) := by
  induction samples generalizing A B with
  | leaf => trivial
  | @node n samples left right ihL ihR =>
    have hp : 0 < 2 ^ n := by positivity
    have hleft := ihL t.2.1 (appendMovingSlotLeaves n (movingCompensationSlots n samples) small.1)
      bulk.1 (4 + A) B (moving_append_length_le n _ _ 4 A
        (moving_compensation_length n samples) hsmall.1) hbulk.1
    have hright := ihR t.2.2 (appendMovingSlotLeaves n (movingCompensationSlots n samples) small.2)
      bulk.2 (4 + A) B (moving_append_length_le n _ _ 4 A
        (moving_compensation_length n samples) hsmall.2) hbulk.2
    have hD : 2 ^ n * (4 + A + B + 4 * n + 4) ≤ 2 ^ (n + 1) * (A + B + 4 * (n + 1) + 4) := by
      rw [pow_succ]
      nlinarith
    have hbase : 2 ^ n * A + 2 ^ n * B ≤ 2 ^ (n + 1) * (A + B + 4 * (n + 1) + 4) := by
      rw [pow_succ]
      nlinarith
    have hcomp : 2 ^ n * 4 ≤ 2 ^ (n + 1) * (A + B + 4 * (n + 1) + 4) := by
      rw [pow_succ]
      nlinarith
    refine ⟨?_, ?_, ?_, hleft.mono hD, hright.mono hD⟩
    · rw [List.length_append]
      exact (Nat.add_le_add (moving_flatten_length_le n _ A hsmall.1)
        (moving_flatten_length_le n _ B hbulk.1)).trans hbase
    · rw [List.length_append]
      exact (Nat.add_le_add (moving_flatten_length_le n _ A hsmall.2)
        (moving_flatten_length_le n _ B hbulk.2)).trans hbase
    · exact (moving_flatten_length_le n _ 4 (moving_compensation_length n samples)).trans hcomp

theorem MovingSlotData.occurrence_size {σ : Type*} {n D : ℕ}
    (T : MovingSlotData σ n) (hT : T.SizeLE D) :
    ∀ o ∈ T.occurrences,
      o.current.lengthLE D ∧ ∀ s ∈ o.path, s.lengthLE D := by
  induction T with
  | leaf => simp [occurrences]
  | @node n s CL CR u left right ihL ihR =>
    intro o ho
    have hb (b : Bool) : (step s CL CR u left right b).lengthLE D :=
      ⟨hT.2.1, hT.1, hT.2.2.1⟩
    rcases List.mem_cons.mp ho with ho | ho
    · subst o
      exact ⟨hb false, by simp⟩
    · rcases List.mem_append.mp ho with ho | ho
      · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
        have h := ihL hT.2.2.2.1 o' ho'
        refine ⟨h.1, ?_⟩
        intro t ht
        rcases List.mem_append.mp ht with ht | ht
        · exact h.2 t ht
        · simpa only [List.mem_singleton.mp ht] using hb true
      · obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
        have h := ihR hT.2.2.2.2 o' ho'
        refine ⟨h.1, ?_⟩
        intro t ht
        rcases List.mem_append.mp ht with ht | ht
        · exact h.2 t ht
        · simpa only [List.mem_singleton.mp ht] using hb false

end Ostmann

end OAI
