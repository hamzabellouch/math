import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FixedSequential

namespace OAI

section

namespace KS.W04.BinaryStackMoves
open KS.W01.FixedStack
open KS.W29 (StackAction)
open KS.W29.FixedSequential (Program ActiveFor HaltsAfter HaltsFromWithin)

variable {k : Nat}

def clearDispatch (port : Fin k) (_state : Fin 1) (heads : Fin k → Fin 3)
    (_coin : Bool) : Instruction k 1 :=
  if (heads port).val = 0 then Instruction.halt k 1
  else ⟨some (0 : Fin 1), Vector.ofFn (fun j => if j = port then .pop else .stay)⟩

def clearMachine (port : Fin k) : Machine := compile 0 port port (clearDispatch port)
def clearProgram (port : Fin k) : Program k :=
  KS.W29.FixedSequential.ofMachine (clearMachine port)

def oneConfig (port : Fin k) (state : Option (Fin 1)) (payload : List Bool)
    (rest : Fin k → List Bool) : Config k 1 :=
  ⟨state, fun j => if j = port then payload else rest j⟩

theorem config_ext {q : Nat} {c d : Config k q} (hs : c.state = d.state)
    (ht : ∀ j, c.«stacks» j = d.«stacks» j) : c = d := by
  cases c
  cases d
  exact congrArg₂ Config.mk hs (funext ht)

theorem clear_step_cons (port : Fin k) (b : Bool) (xs : List Bool)
    (rest : Fin k → List Bool) (coin : Bool) :
    (clearMachine port).step (oneConfig port (some (0 : Fin 1)) (b :: xs) rest) coin =
      oneConfig port (some (0 : Fin 1)) xs rest := by
  unfold clearMachine oneConfig
  erw [step_compile]
  dsimp only [compile]
  cases b <;> apply config_ext
  all_goals
    first | (solve | simp [clearDispatch, observedHeads, KS.W29.topCode]) |
      (intro j; by_cases hj : j = port <;>
      simp [clearDispatch, observedHeads, Instruction.action,
        KS.W29.topCode, StackAction.apply, hj])

theorem clear_step_nil (port : Fin k) (rest : Fin k → List Bool) (coin : Bool) :
    (clearMachine port).step (oneConfig port (some (0 : Fin 1)) [] rest) coin =
      oneConfig port none [] rest := by
  unfold clearMachine oneConfig
  erw [step_compile]
  dsimp only [compile]
  apply config_ext
  · simp [clearDispatch, observedHeads, KS.W29.topCode, Instruction.halt]
  · intro j
    simp [clearDispatch, observedHeads, KS.W29.topCode, Instruction.halt,
      Instruction.action, StackAction.apply]
    all_goals rfl

theorem run_clear (port : Fin k) (xs : List Bool) (rest : Fin k → List Bool)
    (bits : List Bool) (hlen : bits.length = xs.length + 1) :
    (clearMachine port).run (oneConfig port (some (0 : Fin 1)) xs rest) bits =
      oneConfig port none [] rest := by
  induction xs generalizing bits with
  | nil =>
      cases bits with
      | nil => simp at hlen
      | cons coin tail =>
          have ht : tail = [] := by apply List.length_eq_zero_iff.mp; simpa using hlen
          subst tail
          simpa [Machine.run] using clear_step_nil port rest coin
  | cons b xs ih =>
      cases bits with
      | nil => simp at hlen
      | cons coin tail =>
          change (clearMachine port).run ((clearMachine port).step
            (oneConfig port (some 0) (b :: xs) rest) coin) tail = _
          erw [clear_step_cons]
          exact ih tail (by simpa using hlen)

theorem clear_active (port : Fin k) (xs : List Bool) (rest : Fin k → List Bool)
    (bits : List Bool) (hlen : bits.length ≤ xs.length + 1) :
    ActiveFor (clearProgram port) (oneConfig port (some (0 : Fin 1)) xs rest) bits := by
  induction bits generalizing xs with
  | nil => trivial
  | cons coin tail ih =>
      constructor
      · exact Option.some_ne_none _
      · cases xs with
        | nil =>
            have ht : tail = [] := by
              apply List.length_eq_zero_iff.mp
              simp only [List.length_cons, List.length_nil] at hlen
              omega
            subst tail
            trivial
        | cons b xs =>
            change ActiveFor (clearProgram port)
              ((clearMachine port).step (oneConfig port (some (0 : Fin 1)) (b :: xs) rest) coin) tail
            rw [clear_step_cons]
            exact ih xs (by simp only [List.length_cons] at hlen; omega)

theorem clear_haltsAfter (port : Fin k) (xs : List Bool) (rest : Fin k → List Bool)
    (bits : List Bool) (hlen : bits.length = xs.length + 1) :
    HaltsAfter (clearProgram port) (oneConfig port (some (0 : Fin 1)) xs rest) bits := by
  refine ⟨clear_active port xs rest bits hlen.le, ?_⟩
  change ((clearMachine port).run _ bits).state = none
  exact congrArg Config.state (run_clear port xs rest bits hlen)

def moveDispatch (source target : Fin k) (_state : Fin 1) (heads : Fin k → Fin 3)
    (_coin : Bool) : Instruction k 1 :=
  if (heads source).val = 0 then Instruction.halt k 1
  else ⟨some (0 : Fin 1), Vector.ofFn (fun j => if j = source then .pop
    else if j = target then .push ((heads source).val == 2) else .stay)⟩

def moveMachine (source target : Fin k) : Machine :=
  compile 0 source target (moveDispatch source target)
def moveProgram (source target : Fin k) : Program k :=
  KS.W29.FixedSequential.ofMachine (moveMachine source target)

def twoConfig (source target : Fin k) (state : Option (Fin 1))
    (payload destination : List Bool) (rest : Fin k → List Bool) : Config k 1 :=
  ⟨state, fun j => if j = source then payload else if j = target then destination else rest j⟩

theorem move_step_cons (source target : Fin k) (_ : source ≠ target)
    (b : Bool) (xs ys : List Bool) (rest : Fin k → List Bool) (coin : Bool) :
    (moveMachine source target).step (twoConfig source target (some (0 : Fin 1)) (b :: xs) ys rest) coin =
      twoConfig source target (some (0 : Fin 1)) xs (b :: ys) rest := by
  unfold moveMachine twoConfig
  erw [step_compile]
  dsimp only [compile]
  cases b <;> apply config_ext
  all_goals
    first | (solve | simp [moveDispatch, observedHeads, KS.W29.topCode]) |
      (intro j; by_cases hjs : j = source <;> by_cases hjt : j = target <;>
      simp_all [moveDispatch, observedHeads, Instruction.action,
        KS.W29.topCode, StackAction.apply])

theorem move_step_nil (source target : Fin k) (ys : List Bool)
    (rest : Fin k → List Bool) (coin : Bool) :
    (moveMachine source target).step (twoConfig source target (some (0 : Fin 1)) [] ys rest) coin =
      twoConfig source target none [] ys rest := by
  unfold moveMachine twoConfig
  erw [step_compile]
  dsimp only [compile]
  apply config_ext
  · simp [moveDispatch, observedHeads, KS.W29.topCode, Instruction.halt]
  · intro j
    simp [moveDispatch, observedHeads, KS.W29.topCode, Instruction.halt,
      Instruction.action, StackAction.apply]
    all_goals rfl

theorem run_move (source target : Fin k) (hst : source ≠ target)
    (xs ys : List Bool) (rest : Fin k → List Bool) (bits : List Bool)
    (hlen : bits.length = xs.length + 1) :
    (moveMachine source target).run (twoConfig source target (some (0 : Fin 1)) xs ys rest) bits =
      twoConfig source target none [] (xs.reverse ++ ys) rest := by
  induction xs generalizing ys bits with
  | nil =>
      cases bits with
      | nil => simp at hlen
      | cons coin tail =>
          have ht : tail = [] := by apply List.length_eq_zero_iff.mp; simpa using hlen
          subst tail
          simpa [Machine.run] using move_step_nil source target ys rest coin
  | cons b xs ih =>
      cases bits with
      | nil => simp at hlen
      | cons coin tail =>
          change (moveMachine source target).run ((moveMachine source target).step
            (twoConfig source target (some 0) (b :: xs) ys rest) coin) tail = _
          erw [move_step_cons source target hst]
          simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
          exact ih (b :: ys) tail (by simpa using hlen)

theorem move_active (source target : Fin k) (hst : source ≠ target)
    (xs ys : List Bool) (rest : Fin k → List Bool) (bits : List Bool)
    (hlen : bits.length ≤ xs.length + 1) :
    ActiveFor (moveProgram source target) (twoConfig source target (some (0 : Fin 1)) xs ys rest) bits := by
  induction bits generalizing xs ys with
  | nil => trivial
  | cons coin tail ih =>
      constructor
      · exact Option.some_ne_none _
      · cases xs with
        | nil =>
            have ht : tail = [] := by
              apply List.length_eq_zero_iff.mp
              simp only [List.length_cons, List.length_nil] at hlen
              omega
            subst tail
            trivial
        | cons b xs =>
            change ActiveFor (moveProgram source target)
              ((moveMachine source target).step
                (twoConfig source target (some (0 : Fin 1)) (b :: xs) ys rest) coin) tail
            rw [move_step_cons source target hst]
            exact ih xs (b :: ys) (by simp only [List.length_cons] at hlen; omega)

theorem move_haltsAfter (source target : Fin k) (hst : source ≠ target)
    (xs ys : List Bool) (rest : Fin k → List Bool) (bits : List Bool)
    (hlen : bits.length = xs.length + 1) :
    HaltsAfter (moveProgram source target) (twoConfig source target (some (0 : Fin 1)) xs ys rest) bits := by
  refine ⟨move_active source target hst xs ys rest bits hlen.le, ?_⟩
  change ((moveMachine source target).run _ bits).state = none
  exact congrArg Config.state (run_move source target hst xs ys rest bits hlen)

@[simp] theorem oneConfig_original (port : Fin k) (state : Option (Fin 1))
    («stacks» : Fin k → List Bool) : oneConfig port state («stacks» port) «stacks» = ⟨state, «stacks»⟩ := by
  refine config_ext ?_ ?_
  · rfl
  intro j
  by_cases hj : j = port <;> simp [oneConfig, hj]

@[simp] theorem twoConfig_original (source target : Fin k) (state : Option (Fin 1))
    («stacks» : Fin k → List Bool) :
    twoConfig source target state («stacks» source) («stacks» target) «stacks» = ⟨state, «stacks»⟩ := by
  refine config_ext ?_ ?_
  · rfl
  intro j
  by_cases hjs : j = source <;> by_cases hjt : j = target <;>
    simp_all [twoConfig]

theorem run_clear_stacks (port : Fin k) («stacks» : Fin k → List Bool) (bits : List Bool)
    (hlen : bits.length = («stacks» port).length + 1) :
    (clearMachine port).run ⟨some (0 : Fin 1), «stacks»⟩ bits = oneConfig port none [] «stacks» := by
  have h := run_clear port («stacks» port) «stacks» bits hlen
  erw [oneConfig_original] at h
  exact h

theorem run_move_stacks (source target : Fin k) (hst : source ≠ target)
    («stacks» : Fin k → List Bool) (bits : List Bool)
    (hlen : bits.length = («stacks» source).length + 1) :
    (moveMachine source target).run ⟨some (0 : Fin 1), «stacks»⟩ bits =
      twoConfig source target none [] ((«stacks» source).reverse ++ «stacks» target) «stacks» := by
  have h := run_move source target hst («stacks» source) («stacks» target) «stacks» bits hlen
  erw [twoConfig_original] at h
  exact h

theorem clear_haltsAfter_stacks (port : Fin k) («stacks» : Fin k → List Bool)
    (bits : List Bool) (hlen : bits.length = («stacks» port).length + 1) :
    HaltsAfter (clearProgram port) ⟨some (0 : Fin 1), «stacks»⟩ bits := by
  have h := clear_haltsAfter port («stacks» port) «stacks» bits hlen
  rw [oneConfig_original] at h
  exact h

theorem move_haltsAfter_stacks (source target : Fin k) (hst : source ≠ target)
    («stacks» : Fin k → List Bool) (bits : List Bool)
    (hlen : bits.length = («stacks» source).length + 1) :
    HaltsAfter (moveProgram source target) ⟨some (0 : Fin 1), «stacks»⟩ bits := by
  have h := move_haltsAfter source target hst («stacks» source) («stacks» target) «stacks» bits hlen
  rw [twoConfig_original] at h
  exact h

theorem clear_linear_time (port : Fin k) («stacks» : Fin k → List Bool) :
    HaltsFromWithin (clearProgram port) ⟨some (0 : Fin 1), «stacks»⟩ ((«stacks» port).length + 1) := by
  intro bits hlen
  change ((clearMachine port).run _ bits).state = none
  exact congrArg Config.state (run_clear_stacks port «stacks» bits hlen)

theorem move_linear_time (source target : Fin k) (hst : source ≠ target)
    («stacks» : Fin k → List Bool) :
    HaltsFromWithin (moveProgram source target) ⟨some (0 : Fin 1), «stacks»⟩ ((«stacks» source).length + 1) := by
  intro bits hlen
  change ((moveMachine source target).run _ bits).state = none
  exact congrArg Config.state (run_move_stacks source target hst «stacks» bits hlen)

theorem move_output (source target : Fin k) (hst : source ≠ target) (xs bits : List Bool)
    (hlen : bits.length = xs.length + 1) :
    (moveMachine source target).output xs bits = xs.reverse := by
  have hi : (moveMachine source target).init xs =
      twoConfig source target (some (0 : Fin 1)) xs [] (fun _ => []) := by
    refine config_ext ?_ ?_
    · rfl
    intro j
    simp [Machine.init, moveMachine, compile, twoConfig]
    rfl
  unfold Machine.output
  rw [hi]
  have hr := congrArg (fun c : Config k 1 => c.«stacks» target)
    (run_move source target hst xs [] (fun _ => []) bits hlen)
  change ((moveMachine source target).run _ bits).«stacks» target = _
  exact hr.trans (by simp [twoConfig, Ne.symm hst])

theorem clear_table_length (port : Fin k) : (clearMachine port).table.length = 3 ^ k * 2 := by
  simpa [clearMachine] using compile_table_length (0 : Fin 1) port port (clearDispatch port)

theorem move_table_length (source target : Fin k) :
    (moveMachine source target).table.length = 3 ^ k * 2 := by
  simpa [moveMachine] using compile_table_length (0 : Fin 1) source target (moveDispatch source target)

end KS.W04.BinaryStackMoves

end

end OAI
