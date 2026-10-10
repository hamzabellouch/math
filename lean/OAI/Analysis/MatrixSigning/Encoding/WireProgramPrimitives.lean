import Mathlib
import OAI.Analysis.MatrixSigning.Machines.StackTransferSpecs
import OAI.Analysis.MatrixSigning.Machines.FixedCopyRestore

namespace OAI

namespace KS.W15.WireProgram
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def ports3 {k : Nat} (a b c : Fin k) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Fin 3 ↪ Fin k := ⟨![a,b,c], by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all⟩

def copyProgram {k : Nat} (a b c : Fin k) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Program k := KS.W01.FixedCopy.program (ports3 a b c hab hac hbc)

theorem copy_spec {k : Nat} (a b c : Fin k) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (before : Fin k → List Bool) (hb : before b = []) (hc : before c = []) :
    RunSpec (copyProgram a b c hab hac hbc) before
      (Function.update before b (before a)) (2 * (before a).length + 2) := by
  intro bits hlen
  exact KS.W01.FixedCopy.run_copy_restore (ports3 a b c hab hac hbc) before
    (before a) bits rfl hb hc hlen

def transferProgram {k : Nat} (source target scratch : Fin k) : Program k :=
  compose (KS.W04.BinaryStackMoves.moveProgram source scratch)
    (KS.W04.BinaryStackMoves.moveProgram scratch target)

def transferAfter {k : Nat} (source target : Fin k) (before : Fin k → List Bool) :
    Fin k → List Bool :=
  fun j => if j = source then [] else if j = target then before source ++ before target else before j

theorem transfer_spec {k : Nat} (source target scratch : Fin k)
    (hst : source ≠ target) (hs : source ≠ scratch) (ht : target ≠ scratch)
    (before : Fin k → List Bool) (htmp : before scratch = []) :
    RunSpec (transferProgram source target scratch) before (transferAfter source target before)
      (2 * (before source).length + 2) := by
  have h1 := RationalMultiply.move_spec source scratch hs before
  have h2 := RationalMultiply.move_spec scratch target ht.symm
    (RationalMultiply.moveAfter source scratch before)
  have he : RationalMultiply.moveAfter scratch target
      (RationalMultiply.moveAfter source scratch before) = transferAfter source target before := by
    funext j
    by_cases hj : j = source
    · subst j
      simp [RationalMultiply.moveAfter, transferAfter, hs, hst]
    · by_cases hk : j = target
      · subst j
        simp [RationalMultiply.moveAfter, transferAfter, hs.symm, ht, hst.symm, htmp]
      · by_cases hr : j = scratch
        · subst j
          simp [RationalMultiply.moveAfter, transferAfter, hs.symm, ht.symm, htmp]
        · simp [RationalMultiply.moveAfter, transferAfter, hj, hk, hr]
  have h := h1.compose h2
  rw [he] at h
  convert h using 1 <;> (try rfl)
  simp [RationalMultiply.moveAfter, hs.symm, htmp]
  omega

def stayProgram {k : Nat} (port : Fin k) : Program k :=
  ofMachine (compile (0 : Fin 1) port port (fun _ _ _ => Instruction.halt k 1))

theorem stay_spec {k : Nat} (port : Fin k) (before : Fin k → List Bool) :
    RunSpec (stayProgram port) before before 1 := by
  intro bits hlen
  rcases bits with _ | ⟨coin,tail⟩
  · simp at hlen
  have ht : tail = [] := by apply List.length_eq_zero_iff.mp; simpa using hlen
  subst tail
  change (compile (0 : Fin 1) port port (fun _ _ _ => Instruction.halt k 1)).step
    (⟨some (0 : Fin 1),before⟩ : Config k 1) coin = _
  erw [step_compile]
  simp [Instruction.halt, Instruction.action, KS.W29.StackAction.apply]
  rfl

def pushProgram {k : Nat} (port : Fin k) (b : Bool) : Program k :=
  ofMachine (compile (0 : Fin 1) port port (fun _ _ _ =>
    ⟨none,Vector.ofFn (fun j => if j = port then .push b else .stay)⟩))

theorem push_spec {k : Nat} (port : Fin k) (b : Bool) (before : Fin k → List Bool) :
    RunSpec (pushProgram port b) before (Function.update before port (b :: before port)) 1 := by
  intro bits hlen
  rcases bits with _ | ⟨coin,tail⟩
  · simp at hlen
  have ht : tail = [] := by apply List.length_eq_zero_iff.mp; simpa using hlen
  subst tail
  change (compile (0 : Fin 1) port port (fun _ _ _ =>
    ⟨none,Vector.ofFn (fun j => if j = port then .push b else .stay)⟩)).step
    (⟨some (0 : Fin 1),before⟩ : Config k 1) coin = _
  erw [step_compile]
  apply congrArg (Config.mk none)
  funext j
  by_cases hj : j = port <;>
    simp [Instruction.action, KS.W29.StackAction.apply, Function.update, hj]

def literalProgram {k : Nat} (port : Fin k) : List Bool → Program k
  | [] => stayProgram port
  | b :: bs => compose (literalProgram port bs) (pushProgram port b)

theorem literal_spec {k : Nat} (port : Fin k) (word : List Bool)
    (before : Fin k → List Bool) :
    RunSpec (literalProgram port word) before
      (Function.update before port (word ++ before port)) (word.length + 1) := by
  induction word generalizing before with
  | nil => simpa [literalProgram] using stay_spec port before
  | cons b bs ih =>
      have h := (ih before).compose
        (push_spec port b (Function.update before port (bs ++ before port)))
      simpa [literalProgram, List.length_cons, Nat.add_assoc] using h

end KS.W15.WireProgram

end OAI
