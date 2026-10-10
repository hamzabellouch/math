import Mathlib
import OAI.Analysis.MatrixSigning.Machines.BinaryStackMoves
import OAI.Analysis.MatrixSigning.Encoding.FixedPositiveSerializer
import OAI.Analysis.MatrixSigning.Arithmetic.RationalComparePrimitives

namespace OAI

section

abbrev KS.W28.Workspace (k : ℕ) := Fin k → List Bool

namespace KS.W28.BisectionArithmetic
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W28.FixedPositiveSerializer (registers registers_other)

abbrev Workspace (k : ℕ) := Fin k → List Bool

def clearAfter {k : ℕ} (port : Fin k) (registerMap : Workspace k) : Workspace k :=
  Function.update registerMap port []

theorem clear_spec {k : ℕ} (port : Fin k) (registerMap : Workspace k) :
    RunSpec (KS.W04.BinaryStackMoves.clearProgram port) registerMap (clearAfter port registerMap)
      ((registerMap port).length + 1) := by
  intro bits hbits
  have h := KS.W04.BinaryStackMoves.run_clear_stacks port registerMap bits hbits
  change (KS.W04.BinaryStackMoves.clearMachine port).run ⟨some (0 : Fin 1), registerMap⟩ bits = _
  erw [h]
  change KS.W01.FixedStack.Config.mk none _ = KS.W01.FixedStack.Config.mk none _
  apply congrArg (KS.W01.FixedStack.Config.mk none)
  funext j
  simp [clearAfter, Function.update]

def moveAfter {k : ℕ} (source target : Fin k) (registerMap : Workspace k) : Workspace k :=
  fun j => if j = source then [] else if j = target then
    (registerMap source).reverse ++ registerMap target else registerMap j

theorem move_spec {k : ℕ} (source target : Fin k) (hst : source ≠ target)
    (registerMap : Workspace k) :
    RunSpec (KS.W04.BinaryStackMoves.moveProgram source target) registerMap
      (moveAfter source target registerMap) ((registerMap source).length + 1) := by
  intro bits hbits
  exact KS.W04.BinaryStackMoves.run_move_stacks source target hst registerMap bits hbits

theorem copy_spec {k : ℕ} (ports : Fin 3 ↪ Fin k) (registerMap : Workspace k)
    (hdst : registerMap (ports 1) = []) (hscratch : registerMap (ports 2) = []) :
    RunSpec (KS.W01.FixedCopy.program ports) registerMap
      (Function.update registerMap (ports 1) (registerMap (ports 0)))
      (2 * (registerMap (ports 0)).length + 2) := by
  intro bits hbits
  exact KS.W01.FixedCopy.run_copy_restore ports registerMap (registerMap (ports 0)) bits
    rfl hdst hscratch hbits

def addEmitProgram {k : ℕ} (ports : Fin 3 ↪ Fin k) : Program k :=
  ofMachine (lift3 KS.W01.BinaryAdder.machine ports)

def addProgram {k : ℕ} (ports : Fin 3 ↪ Fin k) : Program k :=
  compose (addEmitProgram ports) (FixedPositiveSerializer.reverseProgram ports)

def sumBits (xs ys : List Bool) : List Bool := KS.W01.BinaryAdder.addBits false xs ys

theorem sumBits_value (xs ys : List Bool) :
    KS.W19.bitsValue (sumBits xs ys) = KS.W19.bitsValue xs + KS.W19.bitsValue ys := by
  simpa [sumBits] using KS.W01.BinaryAdder.addBits_correct false xs ys

theorem sumBits_length_le (xs ys : List Bool) :
    (sumBits xs ys).length ≤ max xs.length ys.length + 1 :=
  KS.W01.BinaryAdder.addBits_length_le false xs ys

theorem add_emit_spec {k : ℕ} (ports : Fin 3 ↪ Fin k) (spare : Workspace k)
    (xs ys : List Bool) :
    RunSpec (addEmitProgram ports) (registers ports spare xs ys [])
      (registers ports spare [] [] (sumBits xs ys).reverse)
      (max xs.length ys.length + 1) := by
  intro bits hbits
  change (lift3 KS.W01.BinaryAdder.machine ports).run
    ⟨some (0 : Fin 2), registers ports spare xs ys []⟩ bits = _
  apply lift3_run_eq
  · have hp : project ports (⟨some 0, registers ports spare xs ys []⟩ : Config k 2) =
        KS.W01.BinaryAdder.cfg (some 0) xs ys [] := by
      change KS.W29.Config.mk (some (0 : Fin 2)) _ = KS.W29.Config.mk (some (0 : Fin 2)) _
      apply congrArg (KS.W29.Config.mk (some (0 : Fin 2)))
      funext j
      simp
    erw [hp]
    have h := KS.W01.BinaryAdder.run_add false xs ys [] bits hbits
    change KS.W01.BinaryAdder.machine.run (KS.W01.BinaryAdder.cfg (some 0) xs ys []) bits = _ at h
    erw [h]
    apply congrArg (KS.W29.Config.mk none)
    funext j
    simp [sumBits]
  · intro j hj
    change registers ports spare [] [] (sumBits xs ys).reverse j = registers ports spare xs ys [] j
    rw [registers_other _ _ _ _ _ _ hj, registers_other _ _ _ _ _ _ hj]

theorem add_spec {k : ℕ} (ports : Fin 3 ↪ Fin k) (spare : Workspace k)
    (xs ys : List Bool) :
    RunSpec (addProgram ports) (registers ports spare xs ys [])
      (registers ports spare [] (sumBits xs ys) [])
      (2 * max xs.length ys.length + 3) := by
  have h := (add_emit_spec ports spare xs ys).compose
    (FixedPositiveSerializer.reverse_spec ports spare (sumBits xs ys))
  apply h.mono
  have hl := sumBits_length_le xs ys
  omega

def shiftDispatch {k : ℕ} (a b : Fin k) (_ : Fin 1) (_ : Fin k → Fin 3)
    (_ : Bool) : Instruction k 1 :=
  ⟨none, Vector.ofFn (fun j => if j = a ∨ j = b then .push false else .stay)⟩

def shiftProgram {k : ℕ} (a b : Fin k) : Program k :=
  ofMachine (compile (0 : Fin 1) a b (shiftDispatch a b))

def shiftAfter {k : ℕ} (a b : Fin k) (registerMap : Workspace k) : Workspace k :=
  fun j => if j = a ∨ j = b then false :: registerMap j else registerMap j

theorem shift_spec {k : ℕ} (a b : Fin k) (registerMap : Workspace k) :
    RunSpec (shiftProgram a b) registerMap (shiftAfter a b registerMap) 1 := by
  intro bits hbits
  cases bits with
  | nil => simp at hbits
  | cons coin rest =>
      have hr : rest = [] := List.length_eq_zero_iff.mp (by simpa using hbits)
      subst rest
      change (compile (0 : Fin 1) a b (shiftDispatch a b)).step ⟨some (0 : Fin 1), registerMap⟩ coin = _
      rw [step_compile]
      apply congrArg (Config.mk none)
      funext j
      by_cases hj : j = a ∨ j = b <;>
        simp [shiftDispatch, shiftAfter, Instruction.action, KS.W29.StackAction.apply, hj]

def productRawAfter {k : ℕ} (ports : Fin 7 ↪ Fin k) (registerMap : Workspace k) : Workspace k :=
  KS.W06.RationalCompare.replacePorts ports registerMap (KS.W03.MultiplicationBody.registers (registerMap (ports 0)) []
    (KS.W03.MultiplicationLoop.advance (registerMap (ports 1)) (registerMap (ports 2)))
    (Computability.encodeNat (KS.W19.bitsValue (registerMap (ports 1)) *
      KS.W19.bitsValue (registerMap (ports 2)))) [] [] [])

def productAfter {k : ℕ} (ports : Fin 7 ↪ Fin k) (registerMap : Workspace k) : Workspace k :=
  clearAfter (ports 2) (productRawAfter ports registerMap)

def productProgram {k : ℕ} (ports : Fin 7 ↪ Fin k) : Program k :=
  compose (KS.W29.FixedSequential.liftPorts KS.W06.RationalCompare.productProgram ports)
    (KS.W04.BinaryStackMoves.clearProgram (ports 2))

theorem product_spec {k : ℕ} (ports : Fin 7 ↪ Fin k) (registerMap : Workspace k)
    (h3 : registerMap (ports 3) = []) (h4 : registerMap (ports 4) = [])
    (h5 : registerMap (ports 5) = []) (h6 : registerMap (ports 6) = []) :
    RunSpec (productProgram ports) registerMap (productAfter ports registerMap)
      (17 * ((registerMap (ports 1)).length + (registerMap (ports 2)).length + 2) ^ 2) := by
  have hp : (fun i => registerMap (ports i)) =
      KS.W03.MultiplicationBody.registers (registerMap (ports 0)) (registerMap (ports 1))
        (registerMap (ports 2)) [] [] [] [] := by
    funext i
    fin_cases i <;> simp [KS.W03.MultiplicationBody.registers, h3, h4, h5, h6]
  have hr := KS.W06.RationalCompare.runSpec_liftPorts KS.W06.RationalCompare.productProgram ports registerMap
    (KS.W03.MultiplicationBody.registers (registerMap (ports 0)) []
      (KS.W03.MultiplicationLoop.advance (registerMap (ports 1)) (registerMap (ports 2)))
      (Computability.encodeNat (KS.W19.bitsValue (registerMap (ports 1)) *
        KS.W19.bitsValue (registerMap (ports 2)))) [] [] [])
    (KS.W06.RationalCompare.productTicks (registerMap (ports 1)) (registerMap (ports 2))) (by
      erw [hp]
      exact KS.W06.RationalCompare.product_spec _ _ _)
  have hc := clear_spec (ports 2) (productRawAfter ports registerMap)
  have hh := hr.compose hc
  apply hh.mono
  have ht := KS.W06.RationalCompare.productTicks_le (registerMap (ports 1)) (registerMap (ports 2))
  have hl : (productRawAfter ports registerMap (ports 2)).length =
      (registerMap (ports 1)).length + (registerMap (ports 2)).length := by
    simp [productRawAfter, KS.W03.MultiplicationBody.registers,
      KS.W03.MultiplicationLoop.advance_length]
  rw [hl]
  nlinarith [sq_nonneg ((registerMap (ports 1)).length + (registerMap (ports 2)).length)]

theorem registers_self {k : ℕ} (ports : Fin 3 ↪ Fin k) (registerMap : Workspace k)
    (h2 : registerMap (ports 2) = []) :
    registers ports registerMap (registerMap (ports 0)) (registerMap (ports 1)) [] = registerMap := by
  funext j
  by_cases h0 : j = ports 0
  · subst j; simp
  · by_cases h1 : j = ports 1
    · subst j; simp
    · by_cases h : j = ports 2
      · subst j; simp [h2]
      · simp [registers, h0, h1, h]

def addAfter {k : ℕ} (ports : Fin 3 ↪ Fin k) (registerMap : Workspace k) : Workspace k :=
  registers ports registerMap [] (sumBits (registerMap (ports 0)) (registerMap (ports 1))) []

theorem add_spec_stacks {k : ℕ} (ports : Fin 3 ↪ Fin k) (registerMap : Workspace k)
    (h2 : registerMap (ports 2) = []) :
    RunSpec (addProgram ports) registerMap (addAfter ports registerMap)
      (2 * max (registerMap (ports 0)).length (registerMap (ports 1)).length + 3) := by
  have h := add_spec ports registerMap (registerMap (ports 0)) (registerMap (ports 1))
  rw [registers_self ports registerMap h2] at h
  exact h

@[simp] theorem productAfter_on {k : ℕ} (ports : Fin 7 ↪ Fin k)
    (registerMap : Workspace k) (i : Fin 7) :
    productAfter ports registerMap (ports i) =
      if i = 0 then registerMap (ports 0) else if i = 3 then
        Computability.encodeNat (KS.W19.bitsValue (registerMap (ports 1)) *
          KS.W19.bitsValue (registerMap (ports 2))) else [] := by
  fin_cases i <;>
    simp [productAfter, clearAfter, productRawAfter, Function.update,
      KS.W03.MultiplicationBody.registers, ports.injective.eq_iff]

theorem productAfter_off {k : ℕ} (ports : Fin 7 ↪ Fin k)
    (registerMap : Workspace k) (j : Fin k) (hj : ∀ i, j ≠ ports i) :
    productAfter ports registerMap j = registerMap j := by
  rw [productAfter, clearAfter, Function.update_of_ne (hj 2)]
  exact KS.W06.RationalCompare.replacePorts_off ports registerMap _ j hj

end KS.W28.BisectionArithmetic

end

end OAI
