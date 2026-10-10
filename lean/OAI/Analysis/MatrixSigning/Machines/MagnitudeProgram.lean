import Mathlib
import OAI.Analysis.MatrixSigning.Machines.MachineCombinators
import OAI.Analysis.MatrixSigning.Arithmetic.BinaryAdderCompose

namespace OAI

namespace KS.W01.MagnitudeProgram
open KS.W29
open KS.W03.MachineCombinators
open KS.W01.BinaryAdder

def carryMachine (carry : Bool) : BinaryMachine :=
  normalizedMachine.withEntry
    (Sequential.leftState machine NormalizeOutput.machine (carryState carry))

def result (carry : Bool) (xs : List Bool) : List Bool := addBits carry [] xs

def ticks (carry : Bool) (xs : List Bool) : ℕ := xs.length + 1 + ((result carry xs).length + 1)

theorem result_value (carry : Bool) (xs : List Bool) :
    KS.W19.bitsValue (result carry xs) = KS.W19.bitsValue xs + KS.W19.digit carry := by
  simpa [result, KS.W19.bitsValue] using addBits_correct carry [] xs

theorem ticks_le (carry : Bool) (xs : List Bool) : ticks carry xs ≤ 2 * xs.length + 3 := by
  have h := addBits_length_le carry [] xs
  simp only [List.length_nil, Nat.zero_max] at h
  unfold ticks result
  omega

theorem run_carry (carry : Bool) (xs bits : List Bool)
    (hlen : bits.length = ticks carry xs) :
    (carryMachine carry).run ⟨some (carryMachine carry).initial, ![[], xs, []]⟩ bits =
      ⟨none, ![[], result carry xs, []]⟩ := by
  change (normalizedMachine.withEntry
    (Sequential.leftState machine NormalizeOutput.machine (carryState carry))).run
      ⟨some (carryMachine carry).initial, ![[], xs, []]⟩ bits = _
  erw [BinaryMachine.withEntry_run]
  have hi : (⟨some (carryMachine carry).initial, ![[],xs,[]]⟩ : Config normalizedMachine.states) =
      Sequential.liftLeft machine NormalizeOutput.machine (cfg (some (carryState carry)) [] xs []) := by
    apply congrArg₂ Config.mk
    · rfl
    · funext j; fin_cases j <;> rfl
  erw [hi]
  have hfirst : (bits.take (xs.length + 1)).length = max ([] : List Bool).length xs.length + 1 := by
    simp only [List.length_take, List.length_nil, Nat.zero_max]
    have hh : xs.length + 1 ≤ bits.length := by unfold ticks at hlen; omega
    exact Nat.min_eq_left hh
  have hsecond : (bits.drop (xs.length + 1)).length = (result carry xs).length + 1 := by
    simp only [List.length_drop, hlen, ticks]
    omega
  have h := NormalizeOutput.compose_result machine
    (cfg (some (carryState carry)) [] xs [])
    (bits.take (xs.length + 1)) (bits.drop (xs.length + 1)) [] (result carry xs)
    (BinaryAdder.haltsAfter carry [] xs [] _ hfirst) (by
      rw [run_add carry [] xs [] _ hfirst]
      simp only [List.append_nil]
      rfl) hsecond
  rw [List.take_append_drop] at h
  refine h.trans ?_
  apply congrArg₂ Config.mk
  · rfl
  · funext j; fin_cases j <;> rfl

def program {k : ℕ} (ports : Fin 3 ↪ Fin k) (carry : Bool) : FixedSequential.Program k :=
  FixedSequential.ofMachine (FixedStack.lift3 (carryMachine carry) ports)

theorem runSpec {k : ℕ} (ports : Fin 3 ↪ Fin k) (carry : Bool)
    (store : Fin k → List Bool) (xs : List Bool)
    (hzero : store (ports 0) = []) (hpayload : store (ports 1) = xs)
    (hscratch : store (ports 2) = []) :
    RunSpec (program ports carry) store
      (Function.update store (ports 1) (result carry xs)) (ticks carry xs) := by
  intro bits hbits
  change (FixedStack.lift3 (carryMachine carry) ports).run
    ⟨some (carryMachine carry).initial, store⟩ bits = _
  apply lift3_run_eq
  · have hin : FixedStack.project ports
        (⟨some (carryMachine carry).initial, store⟩ :
          FixedStack.Config k (carryMachine carry).states) =
        ⟨some (carryMachine carry).initial, ![[], xs, []]⟩ := by
      change Config.mk _ (fun j => store (ports j)) = Config.mk _ _
      congr 1
      funext j
      fin_cases j
      · exact hzero
      · exact hpayload
      · exact hscratch
    erw [hin, run_carry carry xs bits hbits]
    congr 1
    funext j
    fin_cases j <;>
      simp [Function.update, ports.injective.eq_iff, hzero, hscratch]
  · intro j hj
    simp [Function.update, hj 1]

theorem runSpec_linear {k : ℕ} (ports : Fin 3 ↪ Fin k) (carry : Bool)
    (store : Fin k → List Bool) (xs : List Bool)
    (hzero : store (ports 0) = []) (hpayload : store (ports 1) = xs)
    (hscratch : store (ports 2) = []) :
    RunSpec (program ports carry) store
      (Function.update store (ports 1) (result carry xs)) (2 * xs.length + 3) :=
  (runSpec ports carry store xs hzero hpayload hscratch).mono (ticks_le carry xs)

end KS.W01.MagnitudeProgram

end OAI
