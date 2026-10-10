import OAI.MathematicalPhysics.NavierStokes.Material.Model

namespace OAI

namespace Alternating

@[simp] theorem configurationAt_zero (I : MachineInput) :
    configurationAt I 0 = initialConfiguration I.2 := rfl

theorem configurationAt_succ (I : MachineInput) (n : ℕ) :
    configurationAt I (n + 1) = I.1.step (configurationAt I n) :=
  Function.iterate_succ_apply' _ _ _

theorem Machine.instruction_bounds {M : Machine} (hM : M.WellFormed)
    {q a : ℕ} {i : Instruction} (hi : M.instruction q a = some i) :
    i.1 < M.stateCount ∧ i.2.1 < M.symbolCount := by
  obtain ⟨row, hr, hi⟩ := Option.bind_eq_some_iff.1 (Option.join_eq_some_iff.1 hi)
  exact (hM.2.2 row (List.mem_of_getElem? hr)).2 i (List.mem_of_getElem? hi)

def Configuration.ValidFor (M : Machine) (c : Configuration) : Prop :=
  c.state ≤ M.stateCount ∧ ∀ j : ℤ, c.tape j < M.symbolCount

theorem initialConfiguration_valid {I : MachineInput} (hI : ValidInput I) :
    (initialConfiguration I.2).ValidFor I.1 := by
  refine ⟨by simp [initialConfiguration], ?_⟩
  intro j
  by_cases hj : j < 0
  · simp [initialConfiguration, hj, Machine.symbolCount]
  · cases ha : I.2[j.toNat]? with
    | none => simp [initialConfiguration, hj, ha, Machine.symbolCount]
    | some a =>
      simpa [initialConfiguration, hj, ha] using hI.2 a (List.mem_of_getElem? ha)

theorem Machine.step_valid {M : Machine} (hM : M.WellFormed) {c : Configuration}
    (hc : c.ValidFor M) : (M.step c).ValidFor M := by
  unfold Machine.step
  split
  · exact hc
  · split
    · exact ⟨le_rfl, hc.2⟩
    · rename_i i hi
      have hi' := M.instruction_bounds hM hi
      refine ⟨hi'.1.le, ?_⟩
      intro j
      by_cases hj : j = c.head
      · simpa [hj] using hi'.2
      · simpa [Function.update_of_ne hj] using hc.2 j

theorem configurationAt_valid {I : MachineInput} (hI : ValidInput I) (n : ℕ) :
    (configurationAt I n).ValidFor I.1 := by
  induction n with
  | zero => exact initialConfiguration_valid hI
  | succ n ih => rw [configurationAt_succ]; exact I.1.step_valid hI.1 ih

theorem Machine.step_head_bounds (M : Machine) (c : Configuration) :
    c.head - 1 ≤ (M.step c).head ∧ (M.step c).head ≤ c.head + 1 := by
  unfold Machine.step
  split
  · simp
  · split
    · simp
    · rename_i i _
      have hi := i.2.2.isLt
      change c.head - 1 ≤ c.head + (i.2.2.val : ℤ) - 1 ∧
        c.head + (i.2.2.val : ℤ) - 1 ≤ c.head + 1
      omega

theorem configurationAt_head_bounds (I : MachineInput) (n : ℕ) :
    -(n : ℤ) ≤ (configurationAt I n).head ∧ (configurationAt I n).head ≤ n := by
  induction n with
  | zero => simp [initialConfiguration]
  | succ n ih =>
    rw [configurationAt_succ]
    have h := I.1.step_head_bounds (configurationAt I n)
    constructor <;> omega

theorem Machine.step_tape_unchanged (M : Machine) (c : Configuration) {j : ℤ}
    (hj : j ≠ c.head) : (M.step c).tape j = c.tape j := by
  unfold Machine.step
  split
  · rfl
  · split
    · rfl
    · simp [Function.update_of_ne hj]

theorem initialConfiguration_tape_outside (w : List ℕ) {j : ℤ}
    (hj : j < 0 ∨ (w.length : ℤ) ≤ j) : (initialConfiguration w).tape j = 0 := by
  by_cases hj0 : j < 0
  · simp [initialConfiguration, hj0]
  · have hlen : w.length ≤ j.toNat := by omega
    simp [initialConfiguration, hj0, List.getElem?_eq_none hlen]

theorem configurationAt_tape_outside (I : MachineInput) (n : ℕ) {j : ℤ}
    (hj : j < -(n : ℤ) ∨ (I.2.length : ℤ) + n ≤ j) :
    (configurationAt I n).tape j = 0 := by
  induction n with
  | zero => exact initialConfiguration_tape_outside I.2 (by simpa using hj)
  | succ n ih =>
    have hhead := configurationAt_head_bounds I n
    have hout : j < -(n : ℤ) ∨ (I.2.length : ℤ) + n ≤ j := by omega
    have hne : j ≠ (configurationAt I n).head := by omega
    rw [configurationAt_succ, I.1.step_tape_unchanged _ hne]
    exact ih hout

theorem Machine.step_of_halted (M : Machine) {c : Configuration}
    (hc : M.isHalting c.state = true) : M.step c = c := by simp [Machine.step, hc]

theorem configurationAt_freezes {I : MachineInput} {n : ℕ}
    (hn : I.1.isHalting (configurationAt I n).state = true) (r : ℕ) :
    configurationAt I (n + r) = configurationAt I n := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [← Nat.add_assoc, configurationAt_succ, ih, I.1.step_of_halted hn]


theorem neZeroThree : NeZero 3 := ⟨Nat.succ_ne_zero 2⟩

def Machine.normalizedInstruction (M : Machine) (q a : ℕ) : Instruction :=
  letI := neZeroThree
  if M.isHalting q then (q, a, 1)
  else (M.instruction q a).getD (M.stateCount, a, 1)

def applyInstruction (c : Configuration) (i : Instruction) : Configuration :=
  { state := i.1
    head := c.head + (i.2.2.val : ℤ) - 1
    tape := Function.update c.tape c.head i.2.1 }

theorem Machine.step_eq_normalized (M : Machine) (c : Configuration) :
    M.step c = applyInstruction c (M.normalizedInstruction c.state (c.tape c.head)) := by
  unfold Machine.step Machine.normalizedInstruction
  split
  · simp [applyInstruction]
  · cases hi : M.instruction c.state (c.tape c.head) with
    | none => simp [applyInstruction]
    | some i => rfl

theorem Machine.normalizedInstruction_bounds {M : Machine} (hM : M.WellFormed)
    {q a : ℕ} (hq : q ≤ M.stateCount) (ha : a < M.symbolCount) :
    (M.normalizedInstruction q a).1 ≤ M.stateCount ∧
      (M.normalizedInstruction q a).2.1 < M.symbolCount := by
  unfold Machine.normalizedInstruction
  split
  · exact ⟨hq, ha⟩
  · cases hi : M.instruction q a with
    | none => exact ⟨le_rfl, ha⟩
    | some i =>
      have hib := M.instruction_bounds hM hi
      exact ⟨hib.1.le, hib.2⟩

end Alternating

end OAI
