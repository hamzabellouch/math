import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.LatticeArithmetic

namespace OAI

/-! The finite lattice lookup table obtained from an actual machine. The
least significant bit of every symbol is a read-only origin marker. Missing
instructions use the existing normalized extra halting state. -/

namespace ForcedComputation.Lattice

def machineBase (M : Alternating.Machine) : ℕ :=
  max 2 (max (2 * M.symbolCount) (M.stateCount + 1))

theorem machineBase_two_le (M : Alternating.Machine) : 2 ≤ machineBase M := le_max_left _ _

theorem machineBase_symbols (M : Alternating.Machine) : 2 * M.symbolCount ≤ machineBase M :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem machineBase_states (M : Alternating.Machine) : M.stateCount + 1 ≤ machineBase M :=
  (le_max_right _ _).trans (le_max_right _ _)

def markedDigit (a : ℕ) (origin : Bool) : ℕ := 2 * a + origin.toNat

theorem markedDigit_symbol (a : ℕ) (origin : Bool) : markedDigit a origin / 2 = a := by
  cases origin with
  | false => simp [markedDigit]
  | true => simp only [markedDigit, Bool.toNat_true]; omega

theorem markedDigit_bit (a : ℕ) (origin : Bool) : markedDigit a origin % 2 = origin.toNat := by
  cases origin <;> simp [markedDigit]

theorem markedDigit_lt {M : Alternating.Machine} {a : ℕ}
    (ha : a < M.symbolCount) (origin : Bool) : markedDigit a origin < machineBase M := by
  have hb := machineBase_symbols M
  cases origin <;> simp [markedDigit] <;> omega

def markedTape (C : Alternating.Configuration) (j : ℤ) : ℕ :=
  markedDigit (C.tape j) (decide (j = 0))

theorem markedTape_symbol (C : Alternating.Configuration) (j : ℤ) :
    markedTape C j / 2 = C.tape j := markedDigit_symbol _ _

theorem markedTape_origin (C : Alternating.Configuration) (j : ℤ) :
    markedTape C j % 2 = 1 ↔ j = 0 := by
  rw [markedTape, markedDigit_bit]
  by_cases hj : j = 0 <;> simp [hj]

theorem markedTape_lt {M : Alternating.Machine} {C : Alternating.Configuration}
    (hC : C.ValidFor M) (j : ℤ) : markedTape C j < machineBase M :=
  markedDigit_lt (hC.2 j) _

def machineRule (M : Alternating.Machine) (hM : M.WellFormed) (q a : ℕ) :
    Option (Rule (machineBase M)) :=
  if hq : q ≤ M.stateCount then
    if ha : a / 2 < M.symbolCount then
      if M.isHalting q then none else
      let r := M.normalizedInstruction q (a / 2)
      some {
        next := ⟨r.1, by
          dsimp only [r]
          have hr := M.normalizedInstruction_bounds hM hq ha
          have hb := machineBase_states M
          omega⟩
        write := ⟨2 * r.2.1 + a % 2, by
          dsimp only [r]
          have hr := M.normalizedInstruction_bounds hM hq ha
          have hb := machineBase_symbols M
          have ha₂ := Nat.mod_lt a (by decide : 0 < 2)
          omega⟩
        move := r.2.2 }
    else none
  else none

def machineTable (M : Alternating.Machine) (hM : M.WellFormed) : Table (machineBase M) where
  rows := List.ofFn fun q : Fin (machineBase M) =>
    List.ofFn fun a : Fin (machineBase M) => machineRule M hM q a
  halting := (List.range (M.stateCount + 1)).filter M.isHalting

theorem machineTable_lookup (M : Alternating.Machine) (hM : M.WellFormed)
    {q a : ℕ} (hq : q < machineBase M) (ha : a < machineBase M) :
    (machineTable M hM).lookup q a = machineRule M hM q a := by
  simp [Table.lookup, machineTable, hq, ha]

theorem machineTable_halting (M : Alternating.Machine) (hM : M.WellFormed)
    {q : ℕ} (hq : q ≤ M.stateCount) :
    q ∈ (machineTable M hM).halting ↔ M.isHalting q = true := by
  have hq' : q < M.stateCount + 1 := by omega
  simp only [machineTable, List.mem_filter, List.mem_range, hq', true_and]

theorem machineRule_halted (M : Alternating.Machine) (hM : M.WellFormed)
    {q a : ℕ} (hh : M.isHalting q = true) : machineRule M hM q a = none := by
  unfold machineRule
  split
  · split
    · simp
    · rfl
  · rfl

theorem machineRule_spec (M : Alternating.Machine) (hM : M.WellFormed)
    {q a : ℕ} (hq : q ≤ M.stateCount) (ha : a / 2 < M.symbolCount)
    (hh : M.isHalting q = false) :
    ∃ r, machineRule M hM q a = some r ∧
      r.next.val = (M.normalizedInstruction q (a / 2)).1 ∧
      r.write.val = 2 * (M.normalizedInstruction q (a / 2)).2.1 + a % 2 ∧
      r.move = (M.normalizedInstruction q (a / 2)).2.2 := by
  simp only [machineRule, dite_eq_left hq, dite_eq_left ha, hh, Bool.false_eq_true, ite_false]
  exact ⟨_, rfl, rfl, rfl, rfl⟩

theorem machineRule_preserves_origin (M : Alternating.Machine) (hM : M.WellFormed)
    {q a : ℕ} (hq : q ≤ M.stateCount) (ha : a / 2 < M.symbolCount)
    (hh : M.isHalting q = false) :
    ∃ r, machineRule M hM q a = some r ∧ r.write.val % 2 = a % 2 ∧
      r.write.val / 2 = (M.normalizedInstruction q (a / 2)).2.1 := by
  obtain ⟨r, hr, _, hw, _⟩ := machineRule_spec M hM hq ha hh
  have ha₂ := Nat.mod_lt a (by decide : 0 < 2)
  refine ⟨r, hr, ?_, ?_⟩ <;> rw [hw] <;> omega

end ForcedComputation.Lattice

end OAI
