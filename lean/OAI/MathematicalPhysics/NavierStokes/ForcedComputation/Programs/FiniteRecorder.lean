import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.RecorderMachine

namespace OAI

/-! A genuinely finite recorder alphabet and control set for a well-formed
machine. The extra state is the normalized missing-instruction halt state. -/

namespace ForcedComputation.Recorder

open History Control

abbrev State (M : Alternating.Machine) := Fin (M.stateCount + 1)
abbrev Alphabet (M : Alternating.Machine) := Fin M.symbolCount

def finiteMachine (M : Alternating.Machine) (hM : M.WellFormed) :
    Machine (State M) (Alphabet M) where
  halting := fun q => M.isHalting q.val
  next := fun q a => ⟨(M.normalizedInstruction q.val a.val).1,
    Nat.lt_succ_of_le (M.normalizedInstruction_bounds hM (Nat.le_of_lt_succ q.isLt) a.isLt).1⟩
  write := fun q a => ⟨(M.normalizedInstruction q.val a.val).2.1,
    (M.normalizedInstruction_bounds hM (Nat.le_of_lt_succ q.isLt) a.isLt).2⟩
  move := fun q a => ((M.normalizedInstruction q.val a.val).2.2.val : ℤ) - 1
  move_bound := by
    intro q a
    have h := (M.normalizedInstruction q.val a.val).2.2.isLt
    constructor <;> omega

def forgetWork {M : Alternating.Machine} (C : WorkConfiguration (State M) (Alphabet M)) :
    WorkConfiguration ℕ ℕ :=
  ⟨C.state.val, C.head, fun j => (C.tape j).val⟩

theorem forgetWork_next (M : Alternating.Machine) (hM : M.WellFormed)
    (C : WorkConfiguration (State M) (Alphabet M)) :
    forgetWork (workNext (finiteMachine M hM) C) = workNext (ofMachine M) (forgetWork C) := by
  cases C with
  | mk q h t =>
    simp only [forgetWork, workNext, finiteMachine, ofMachine]
    congr 1
    funext j
    by_cases hj : j = h <;> simp [hj]

def initialState (M : Alternating.Machine) : State M := ⟨0, by simp⟩

def initialAlphabet (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) :
    ℤ → Alphabet I.1 :=
  fun j => ⟨(Alternating.initialConfiguration I.2).tape j,
    (Alternating.initialConfiguration_valid hI).2 j⟩

theorem finite_workAt (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) (n : ℕ) :
    forgetWork (workAt (finiteMachine I.1 hI.1) (initialState I.1) (initialAlphabet I hI) n) =
      originalConfiguration (Alternating.configurationAt I n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [workAt_succ, forgetWork_next, Alternating.configurationAt_succ,
      originalConfiguration_step, ih]

def finiteInitializedRecorder (I : Alternating.MachineInput) (hI : Alternating.ValidInput I) :
    Configuration (State I.1) (Alphabet I.1) :=
  checkpointAt (finiteMachine I.1 hI.1) (initialState I.1) (initialAlphabet I hI) 2 0

theorem finite_recorder_halts_iff (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) :
    (∃ m C q, Steps (finiteMachine I.1 hI.1) m (finiteInitializedRecorder I hI) C ∧
      C.control = Control.checkpoint q ∧ I.1.isHalting q.val = true) ↔ Alternating.Halts I := by
  change (∃ m C q, Steps (finiteMachine I.1 hI.1) m
    (checkpointAt (finiteMachine I.1 hI.1) (initialState I.1) (initialAlphabet I hI) 2 0) C ∧
      C.control = Control.checkpoint q ∧ (finiteMachine I.1 hI.1).halting q = true) ↔ _
  rw [halting_checkpoint_iff _ _ _ 2 (by norm_num)]
  have hs (n : ℕ) := congrArg WorkConfiguration.state (finite_workAt I hI n)
  simp only [forgetWork, originalConfiguration] at hs
  change (∃ n, I.1.isHalting
    (workAt (finiteMachine I.1 hI.1) (initialState I.1) (initialAlphabet I hI) n).state.val = true) ↔ _
  simp only [hs, Alternating.Halts]

def allControls (M : Alternating.Machine) : List (Control (State M) (Alphabet M)) :=
  let states := List.finRange (M.stateCount + 1)
  let letters := List.finRange M.symbolCount
  states.map checkpoint ++
    states.flatMap (fun q => letters.flatMap fun a => [mark (q, a), scanRight (q, a)]) ++
    states.map advance ++ states.map scanLeft

def allHistories (M : Alternating.Machine) : List (History (State M) (Alphabet M)) :=
  [empty, frontier] ++ (List.finRange (M.stateCount + 1)).flatMap
    fun q => (List.finRange M.symbolCount).map fun a => History.record (q, a)

def allSymbols (M : Alternating.Machine) : List (Symbol (State M) (Alphabet M)) :=
  (List.finRange M.symbolCount).flatMap fun a =>
    (allHistories M).flatMap fun l => [false, true].map fun b => (a, l, b)

theorem mem_allControls (M : Alternating.Machine) (q : Control (State M) (Alphabet M)) :
    q ∈ allControls M := by
  cases q with
  | checkpoint q => simp [allControls]
  | mark r => rcases r with ⟨q, a⟩; simp [allControls]
  | scanRight r => rcases r with ⟨q, a⟩; simp [allControls]
  | advance q => simp [allControls]
  | scanLeft q => simp [allControls]

theorem mem_allHistories (M : Alternating.Machine) (l : History (State M) (Alphabet M)) :
    l ∈ allHistories M := by
  cases l with
  | empty => simp [allHistories]
  | frontier => simp [allHistories]
  | record r => rcases r with ⟨q, a⟩; simp [allHistories]

theorem mem_allSymbols (M : Alternating.Machine) (s : Symbol (State M) (Alphabet M)) :
    s ∈ allSymbols M := by
  rcases s with ⟨a, l, b⟩
  apply List.mem_flatMap.mpr
  refine ⟨a, by simp, List.mem_flatMap.mpr ?_⟩
  refine ⟨l, mem_allHistories M l, List.mem_map.mpr ?_⟩
  exact ⟨b, by cases b <;> simp, rfl⟩

/-- Enumerate all control/read-symbol pairs by finite loops and execute the
seven-row local interpreter. This is the finite table used by the geometry. -/
def instructionTable (M : Alternating.Machine) (hM : M.WellFormed) :
    List ((Control (State M) (Alphabet M) × Symbol (State M) (Alphabet M)) ×
      (Control (State M) (Alphabet M) × Symbol (State M) (Alphabet M) × ℤ)) :=
  ((allControls M).flatMap fun q => (allSymbols M).map fun s => (q, s)).filterMap
    fun p => (evalLocal (finiteMachine M hM) p.1 p.2).map fun out => (p, out)

theorem evalLocal_sound {Q A : Type*} [DecidableEq Q] [DecidableEq A]
    {M : Machine Q A} {q q' : Control Q A} {s s' : Symbol Q A} {d : ℤ}
    (he : evalLocal M q s = some (q', s', d)) : LocalStep M q s q' s' d := by
  rcases s with ⟨a, l, b⟩
  cases q with
  | checkpoint q =>
    cases b with
    | true => simp [evalLocal] at he
    | false =>
      simp only [evalLocal] at he
      split at he
      · rename_i hguard
        obtain ⟨hq, hl⟩ := hguard
        have hh := Option.some.inj he
        simp only [Prod.mk.injEq] at hh
        rcases hh with ⟨hq', hs', hd'⟩
        subst_vars
        exact LocalStep.work q a l hq hl
      · simp at he
  | mark r =>
    cases b with
    | true => simp [evalLocal] at he
    | false =>
      simp only [evalLocal] at he
      split at he
      · rename_i hl
        have hh := Option.some.inj he
        simp only [Prod.mk.injEq] at hh
        rcases hh with ⟨hq', hs', hd'⟩
        subst_vars
        exact LocalStep.setMark r a l hl
      · simp at he
  | scanRight r =>
    cases b with
    | true => simp [evalLocal] at he
    | false =>
      simp only [evalLocal] at he
      split at he
      · rename_i hl
        subst l
        have hh := Option.some.inj he
        simp only [Prod.mk.injEq] at hh
        rcases hh with ⟨hq', hs', hd'⟩
        subst_vars
        exact LocalStep.record r a
      · rename_i hl
        have hh := Option.some.inj he
        simp only [Prod.mk.injEq] at hh
        rcases hh with ⟨hq', hs', hd'⟩
        subst_vars
        exact LocalStep.right r a l hl
  | advance q =>
    cases b with
    | true => cases l <;> simp [evalLocal] at he
    | false =>
      cases l with
      | empty =>
        simp only [evalLocal] at he
        have hh := Option.some.inj he
        simp only [Prod.mk.injEq] at hh
        rcases hh with ⟨hq', hs', hd'⟩
        subst_vars
        exact LocalStep.advance q a
      | frontier => simp [evalLocal] at he
      | record r => simp [evalLocal] at he
  | scanLeft q =>
    simp only [evalLocal] at he
    split at he
    · rename_i hl
      cases b with
      | false =>
        simp only [Bool.false_eq_true, ite_false] at he
        have hh := Option.some.inj he
        simp only [Prod.mk.injEq] at hh
        rcases hh with ⟨hq', hs', hd'⟩
        subst_vars
        exact LocalStep.left q a l hl
      | true =>
        simp only [ite_true] at he
        have hh := Option.some.inj he
        simp only [Prod.mk.injEq] at hh
        rcases hh with ⟨hq', hs', hd'⟩
        subst_vars
        exact LocalStep.clearMark q a l hl
    · simp at he

theorem localStep_mem_instructionTable (M : Alternating.Machine) (hM : M.WellFormed)
    {q q' : Control (State M) (Alphabet M)} {s s' : Symbol (State M) (Alphabet M)} {d : ℤ}
    (h : LocalStep (finiteMachine M hM) q s q' s' d) :
    ((q, s), (q', s', d)) ∈ instructionTable M hM := by
  apply List.mem_filterMap.mpr
  refine ⟨(q, s), List.mem_flatMap.mpr ?_, ?_⟩
  · exact ⟨q, mem_allControls M q, List.mem_map.mpr ⟨s, mem_allSymbols M s, rfl⟩⟩
  · simp only [h.eval, Option.map_some]

theorem mem_instructionTable_iff (M : Alternating.Machine) (hM : M.WellFormed)
    {q q' : Control (State M) (Alphabet M)} {s s' : Symbol (State M) (Alphabet M)} {d : ℤ} :
    ((q, s), (q', s', d)) ∈ instructionTable M hM ↔
      LocalStep (finiteMachine M hM) q s q' s' d := by
  constructor
  · intro h
    obtain ⟨p, _, hp⟩ := List.mem_filterMap.mp h
    cases he : evalLocal (finiteMachine M hM) p.1 p.2 with
    | none => simp [he] at hp
    | some output =>
      simp only [he, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact evalLocal_sound he
  · exact localStep_mem_instructionTable M hM

end ForcedComputation.Recorder

end OAI
