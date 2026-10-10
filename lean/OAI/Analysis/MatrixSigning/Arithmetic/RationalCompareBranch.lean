import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FixedBranch
import OAI.Analysis.MatrixSigning.Machines.MagnitudeProgram
import OAI.Analysis.MatrixSigning.Machines.FixedCompare

namespace OAI

namespace KS.W06.RationalCompare
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def stayActions (k : ℕ) : Vector KS.W29.StackAction k := Vector.ofFn (fun _ => .stay)

theorem branch_spec_left {k : ℕ} (P Q : Program k) (output : Fin k)
    (select : (Fin k → Fin 3) → Bool → KS.W29.FixedBranch.SelectInstruction k)
    (before after : Fin k → List Bool) (ticks : ℕ)
    (hselect : ∀ coin, select (observedHeads
      (⟨some (KS.W29.FixedBranch.start P Q), before⟩ : Config k (P.states + Q.states + 1))) coin =
      ⟨.left, stayActions k⟩)
    (hP : RunSpec P before after ticks) :
    RunSpec (KS.W29.FixedBranch.branch P Q output select) before after (ticks + 1) := by
  intro bits hbits
  cases bits with
  | nil => simp at hbits
  | cons coin rest =>
    have hr : rest.length = ticks := by simpa using hbits
    rw [Machine.run]
    erw [KS.W29.FixedBranch.step_start]
    rw [hselect coin]
    simp only [KS.W29.FixedBranch.selectInstruction, Instruction.action,
      stayActions, Vector.getElem_ofFn, KS.W29.StackAction.apply]
    change (KS.W29.FixedBranch.branch P Q output select).toMachine.run
      (KS.W29.FixedBranch.liftLeft P Q ⟨some P.initial, before⟩) rest = _
    rw [KS.W29.FixedBranch.run_left]
    exact congrArg (KS.W29.FixedBranch.liftLeft P Q) (hP rest hr)

theorem branch_spec_right {k : ℕ} (P Q : Program k) (output : Fin k)
    (select : (Fin k → Fin 3) → Bool → KS.W29.FixedBranch.SelectInstruction k)
    (before after : Fin k → List Bool) (ticks : ℕ)
    (hselect : ∀ coin, select (observedHeads
      (⟨some (KS.W29.FixedBranch.start P Q), before⟩ : Config k (P.states + Q.states + 1))) coin =
      ⟨.right, stayActions k⟩)
    (hQ : RunSpec Q before after ticks) :
    RunSpec (KS.W29.FixedBranch.branch P Q output select) before after (ticks + 1) := by
  intro bits hbits
  cases bits with
  | nil => simp at hbits
  | cons coin rest =>
    have hr : rest.length = ticks := by simpa using hbits
    rw [Machine.run]
    erw [KS.W29.FixedBranch.step_start]
    rw [hselect coin]
    simp only [KS.W29.FixedBranch.selectInstruction, Instruction.action,
      stayActions, Vector.getElem_ofFn, KS.W29.StackAction.apply]
    change (KS.W29.FixedBranch.branch P Q output select).toMachine.run
      (KS.W29.FixedBranch.liftRight P Q ⟨some Q.initial, before⟩) rest = _
    rw [KS.W29.FixedBranch.run_right]
    exact congrArg (KS.W29.FixedBranch.liftRight P Q) (hQ rest hr)

def signSelect {k : ℕ} (signPort : Fin k) (heads : Fin k → Fin 3)
    (_ : Bool) : KS.W29.FixedBranch.SelectInstruction k :=
  ⟨if (heads signPort).val = 2 then .right else .left, stayActions k⟩

def magnitudeProgram {k : ℕ} (ports : Fin 3 ↪ Fin k) (signPort : Fin k) : Program k :=
  KS.W29.FixedBranch.branch (KS.W01.MagnitudeProgram.program ports false)
    (KS.W01.MagnitudeProgram.program ports true) (ports 1) (signSelect signPort)

theorem magnitude_spec {k : ℕ} (ports : Fin 3 ↪ Fin k) (signPort : Fin k)
    (before : Fin k → List Bool) (sign : Bool) (xs : List Bool)
    (hsign : before signPort = [sign]) (hzero : before (ports 0) = [])
    (hpayload : before (ports 1) = xs) (hscratch : before (ports 2) = []) :
    RunSpec (magnitudeProgram ports signPort) before
      (Function.update before (ports 1) (KS.W01.MagnitudeProgram.result sign xs))
      (2 * xs.length + 4) := by
  have h := KS.W01.MagnitudeProgram.runSpec_linear ports sign before xs hzero hpayload hscratch
  cases sign
  · apply branch_spec_left _ _ _ _ _ _ (2 * xs.length + 3) _ h
    intro coin
    simp [signSelect, observedHeads, hsign, KS.W29.topCode]
  · apply branch_spec_right _ _ _ _ _ _ (2 * xs.length + 3) _ h
    intro coin
    simp [signSelect, observedHeads, hsign, KS.W29.topCode]

def signedCrossLE (negativeLeft negativeRight : Bool) (left right : ℕ) : Bool :=
  if negativeLeft then
    if negativeRight then decide (right ≤ left) else true
  else if negativeRight then false else decide (left ≤ right)

def compareSelect {k : ℕ} (signLeft signRight output : Fin k)
    (heads : Fin k → Fin 3) (_ : Bool) : KS.W29.FixedBranch.SelectInstruction k :=
  let a := (heads signLeft).val == 2
  let b := (heads signRight).val == 2
  if a = b then ⟨if a then .right else .left, stayActions k⟩
  else ⟨.halt, Vector.ofFn (fun j => if j = output then .push a else .stay)⟩

def swapFirstTwo : Fin 3 ↪ Fin 3 := ⟨![1,0,2], by decide⟩

def signedCompareProgram {k : ℕ} (ports : Fin 3 ↪ Fin k)
    (signLeft signRight : Fin k) : Program k :=
  KS.W29.FixedBranch.branch (KS.W28.FixedCompare.program ports)
    (KS.W28.FixedCompare.program (swapFirstTwo.trans ports)) (ports 2)
    (compareSelect signLeft signRight (ports 2))

def signedCompareAfter {k : ℕ} (ports : Fin 3 ↪ Fin k) (before : Fin k → List Bool)
    (a b : Bool) : Fin k → List Bool :=
  if a = b then
    if a then KS.W28.FixedCompare.after (swapFirstTwo.trans ports) before
      (decide (KS.W19.bitsValue (before (ports 1)) ≤ KS.W19.bitsValue (before (ports 0))))
    else KS.W28.FixedCompare.after ports before
      (decide (KS.W19.bitsValue (before (ports 0)) ≤ KS.W19.bitsValue (before (ports 1))))
  else Function.update before (ports 2) (a :: before (ports 2))

theorem signedCompare_spec {k : ℕ} (ports : Fin 3 ↪ Fin k) (signLeft signRight : Fin k)
    (before : Fin k → List Bool) (a b : Bool)
    (ha : before signLeft = [a]) (hb : before signRight = [b]) :
    RunSpec (signedCompareProgram ports signLeft signRight) before
      (signedCompareAfter ports before a b)
      ((before (ports 0)).length + (before (ports 1)).length + 2) := by
  cases a <;> cases b
  · have h := KS.W28.FixedCompare.compare_spec_linear ports before
    apply branch_spec_left _ _ _ _ _ _ _ _ h
    intro coin
    simp [compareSelect, observedHeads, ha, hb, KS.W29.topCode]
  · intro bits hbits
    cases bits with
    | nil => simp at hbits
    | cons coin rest =>
      rw [Machine.run]
      erw [KS.W29.FixedBranch.step_start]
      simp only [compareSelect, observedHeads, ha, hb, KS.W29.topCode]
      erw [Machine.run_halted _ _ rfl]
      apply congrArg (Config.mk none)
      funext j
      by_cases hj : j = ports 2 <;>
        simp [KS.W29.FixedBranch.selectInstruction, Instruction.action,
          KS.W29.StackAction.apply, signedCompareAfter, Function.update, hj]
  · intro bits hbits
    cases bits with
    | nil => simp at hbits
    | cons coin rest =>
      rw [Machine.run]
      erw [KS.W29.FixedBranch.step_start]
      simp only [compareSelect, observedHeads, ha, hb, KS.W29.topCode]
      erw [Machine.run_halted _ _ rfl]
      apply congrArg (Config.mk none)
      funext j
      by_cases hj : j = ports 2 <;>
        simp [KS.W29.FixedBranch.selectInstruction, Instruction.action,
          KS.W29.StackAction.apply, signedCompareAfter, Function.update, hj]
  · have h := KS.W28.FixedCompare.compare_spec_linear (swapFirstTwo.trans ports) before
    have h' := branch_spec_right (KS.W28.FixedCompare.program ports)
      (KS.W28.FixedCompare.program (swapFirstTwo.trans ports)) (ports 2)
      (compareSelect signLeft signRight (ports 2)) before _ _ (by
        intro coin
        simp [compareSelect, observedHeads, ha, hb, KS.W29.topCode]) h
    convert h' using 1 <;>
      simp [signedCompareProgram, signedCompareAfter, swapFirstTwo, Nat.add_comm]
    omega

theorem signedCompareAfter_output {k : ℕ} (ports : Fin 3 ↪ Fin k)
    (before : Fin k → List Bool) (a b : Bool) :
    signedCompareAfter ports before a b (ports 2) =
      signedCrossLE a b (KS.W19.bitsValue (before (ports 0)))
        (KS.W19.bitsValue (before (ports 1))) :: before (ports 2) := by
  cases a <;> cases b <;>
    simp [signedCompareAfter, signedCrossLE, KS.W28.FixedCompare.after,
      swapFirstTwo, ports.injective.eq_iff]

end KS.W06.RationalCompare

end OAI
