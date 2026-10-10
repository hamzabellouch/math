import OAI.MathematicalPhysics.NavierStokes.Material.Machines

namespace OAI

/-! A fresh initial state, with no incoming machine transition. It performs
one stationary step before simulating the supplied machine. This lets a
periodically repeated loader occupy an otherwise unused incoming branch. -/

namespace ForcedComputation
open Alternating

def shiftInstruction (i : Alternating.Instruction) : Alternating.Instruction :=
  (i.1 + 1, i.2)

def freshMachine (M : Alternating.Machine) : Alternating.Machine :=
  letI := Alternating.neZeroThree
  (M.1 + 1, M.2.1, M.haltingStates.image Nat.succ,
    ((List.range M.symbolCount).map fun a => some (1, a, (1 : Fin 3))) ::
      M.table.map (List.map (Option.map shiftInstruction)))

abbrev freshInput (I : MachineInput) : MachineInput := (freshMachine I.1, I.2)

@[simp] theorem freshMachine_stateCount (M : Alternating.Machine) :
    (freshMachine M).stateCount = M.stateCount + 1 := rfl

@[simp] theorem freshMachine_symbolCount (M : Alternating.Machine) :
    (freshMachine M).symbolCount = M.symbolCount := rfl

theorem freshMachine_wellFormed {M : Alternating.Machine} (hM : M.WellFormed) :
    (freshMachine M).WellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [freshMachine, Machine.table, Machine.stateCount] using congrArg Nat.succ hM.1
  · intro q hq
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
    exact Nat.succ_lt_succ (hM.2.1 r hr)
  · intro row hrow
    change row ∈ _ :: _ at hrow
    rcases List.mem_cons.mp hrow with rfl | hrow
    · refine ⟨by simp, ?_⟩
      intro i hi
      obtain ⟨a, ha, he⟩ := List.mem_map.mp hi
      have he' := Option.some.inj he
      subst i
      exact ⟨by change 1 < M.1 + 1 + 1; omega, List.mem_range.mp ha⟩
    · obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hrow
      obtain ⟨hlen, hib⟩ := hM.2.2 old hold
      refine ⟨by simpa using hlen, ?_⟩
      intro i hi
      obtain ⟨oi, hoi, he⟩ := List.mem_map.mp hi
      cases oi with
      | none => simp at he
      | some j =>
        have he' := Option.some.inj he
        subst i
        have hj := hib j hoi
        exact ⟨Nat.succ_lt_succ hj.1, hj.2⟩

theorem freshInput_valid {I : MachineInput} (hI : Alternating.ValidInput I) :
    Alternating.ValidInput (freshInput I) :=
  ⟨freshMachine_wellFormed hI.1, hI.2⟩

theorem freshInput_wellFormed {I : MachineInput} (hI : Alternating.ValidInput I) :
    (freshMachine I.1).WellFormed :=
  freshMachine_wellFormed (Alternating.ValidInput.machine_wellFormed hI)

@[simp] theorem freshMachine_not_halting_zero (M : Alternating.Machine) :
    (freshMachine M).isHalting 0 = false := by
  simp [Machine.isHalting, freshMachine, Machine.stateCount, Machine.haltingStates]

@[simp] theorem freshMachine_halting_succ (M : Alternating.Machine) (q : ℕ) :
    (freshMachine M).isHalting (q + 1) = M.isHalting q := by
  apply Bool.eq_iff_iff.mpr
  simp [Machine.isHalting, freshMachine, Machine.stateCount, Machine.haltingStates]
  exact (decide_eq_true_iff (p := q = M.1 + 1 ∨ q ∈ M.2.2.1)).symm

theorem freshMachine_instruction_zero (M : Alternating.Machine) {a : ℕ}
    (ha : a < M.symbolCount) :
    (freshMachine M).instruction 0 a = some (1, a, (1 : Fin 3)) := by
  simp [Machine.instruction, freshMachine, Machine.table, ha]

theorem freshMachine_instruction_succ (M : Alternating.Machine) (q a : ℕ) :
    (freshMachine M).instruction (q + 1) a =
      (M.instruction q a).map shiftInstruction := by
  simp only [Machine.instruction, freshMachine, Machine.table, List.getElem?_cons_succ,
    List.getElem?_map]
  cases hr : M.table[q]? with
  | none => simp [Machine.table] at hr; simp [hr]
  | some row =>
    simp only [Machine.table] at hr
    simp only [hr, Option.map_some, Option.bind_some, List.getElem?_map]
    cases row[a]? <;> rfl

def liftConfiguration (c : Alternating.Configuration) : Alternating.Configuration :=
  ⟨c.state + 1, c.head, c.tape⟩

theorem freshMachine_step_lift (M : Alternating.Machine) (c : Alternating.Configuration) :
    (freshMachine M).step (liftConfiguration c) = liftConfiguration (M.step c) := by
  simp only [Machine.step, liftConfiguration, freshMachine_halting_succ]
  cases hh : M.isHalting c.state with
  | true => simp
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, freshMachine_instruction_succ]
    cases hi : M.instruction c.state (c.tape c.head) with
    | none => simp [freshMachine_stateCount]
    | some i => rfl

theorem freshMachine_initial_step {I : MachineInput} (hI : Alternating.ValidInput I) :
    (freshMachine I.1).step (initialConfiguration I.2) =
      liftConfiguration (initialConfiguration I.2) := by
  have ha := (initialConfiguration_valid hI).2 0
  rw [Machine.step]
  simp only [show (initialConfiguration I.2).state = 0 from rfl,
    show (initialConfiguration I.2).head = 0 from rfl,
    freshMachine_not_halting_zero, Bool.false_eq_true, ↓reduceIte]
  rw [freshMachine_instruction_zero I.1 ha]
  simp [liftConfiguration, initialConfiguration]

theorem freshInput_configuration {I : MachineInput} (hI : Alternating.ValidInput I) (n : ℕ) :
    configurationAt (freshInput I) (n + 1) = liftConfiguration (configurationAt I n) := by
  induction n with
  | zero => exact freshMachine_initial_step hI
  | succ n ih =>
    rw [configurationAt_succ, ih, configurationAt_succ]
    exact freshMachine_step_lift I.1 _

theorem freshInput_halts_iff {I : MachineInput} (hI : Alternating.ValidInput I) :
    Alternating.Halts (freshInput I) ↔ Alternating.Halts I := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => simp [freshInput, initialConfiguration] at hn
    | succ n =>
      rw [freshInput_configuration hI] at hn
      exact ⟨n, by simpa [freshInput, liftConfiguration] using hn⟩
  · rintro ⟨n, hn⟩
    refine ⟨n + 1, ?_⟩
    rw [freshInput_configuration hI]
    simpa [freshInput, liftConfiguration] using hn

theorem freshMachine_no_incoming {M : Alternating.Machine} {q a : ℕ}
    {i : Alternating.Instruction} (hi : (freshMachine M).instruction q a = some i) :
    i.1 ≠ 0 := by
  cases q with
  | zero =>
    unfold Machine.instruction freshMachine Machine.table at hi
    simp only [List.getElem?_cons_zero, Option.bind_some, List.getElem?_map] at hi
    cases ha : (List.range M.symbolCount)[a]? with
    | none => simp [ha] at hi
    | some b =>
      simp only [ha, Option.map_some, Option.join_some, Option.some.injEq] at hi
      subst i
      norm_num
  | succ q =>
    rw [freshMachine_instruction_succ] at hi
    obtain ⟨j, _, rfl⟩ := Option.map_eq_some_iff.mp hi
    exact Nat.succ_ne_zero _

end ForcedComputation

end OAI
