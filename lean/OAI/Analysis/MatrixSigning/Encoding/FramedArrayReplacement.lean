import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FixedPortRunSpec
import OAI.Analysis.MatrixSigning.Machines.StackTransferSpecs
import OAI.Analysis.MatrixSigning.Encoding.ReusableArrayLookup
import OAI.Analysis.MatrixSigning.Encoding.FramedArrayPrefix

namespace OAI

namespace KS.W11.FramedArrayRewrite
open KS.W01.FixedStack KS.W03.MachineCombinators
open KS.W29.FixedSequential
open KS.W04.ReusableArrayLookup (run_halted_of_length_ge run_compose_bounded)

def skipPorts : Fin 4 ↪ Fin 5 where
  toFun j := if j = 0 then 0 else if j = 1 then 1 else if j = 2 then 2 else 4
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

def skipProgram : Program 5 :=
  KS.W29.FixedSequential.liftPorts KS.W11.FramedArray.skipProgram skipPorts

def reverseNew : Program 5 := KS.W04.BinaryStackMoves.moveProgram 1 3
def insertNew : Program 5 := KS.W04.BinaryStackMoves.moveProgram 3 0
def restorePrefix : Program 5 := KS.W04.BinaryStackMoves.moveProgram 2 0
def insertAndRestore : Program 5 := compose insertNew restorePrefix
def finishProgram : Program 5 := compose reverseNew insertAndRestore
def replaceTailProgram : Program 5 := compose skipProgram finishProgram

def program : Program 5 := compose prefixProgram replaceTailProgram

theorem program_states : program.states = 8 := rfl
theorem program_input : program.input = 0 := rfl
theorem program_output : program.output = 0 := rfl

theorem program_table_length : program.table.length = 3888 := by
  have generic {k : ℕ} (P Q : Program k) :
      (compose P Q).table.length = ((P.states+Q.states)*3^k)*2 := by
    change (compile (leftState P Q P.initial) P.input Q.output (dispatch P Q)).table.length = _
    rw [compile_table_length]
    simp only [Nat.mul_assoc]
  exact generic prefixProgram replaceTailProgram

theorem run_prefix («prefix» : List (List Bool)) (tail replacement bits : List Bool)
    (hlen : KS.W11.FramedArray.scanFuel «prefix» ≤ bits.length) :
    prefixProgram.toMachine.run
      (config (some prefixProgram.initial) («prefix».flatMap KS.W01.frame ++ tail)
        replacement [] [] (List.replicate «prefix».length true)) bits =
      config none tail replacement («prefix».flatMap KS.W01.frame).reverse [] [] := by
  apply run_halted_of_length_ge prefixProgram.toMachine _ _
    (KS.W11.FramedArray.scanFuel «prefix») rfl _ bits hlen
  intro bs hb
  simpa only [List.append_nil] using transfer_prefix «prefix» tail replacement [] [] bs hb

theorem run_skip (old tail replacement «prefix» scratch bits : List Bool)
    (hlen : 2 * old.length + 1 ≤ bits.length) :
    skipProgram.toMachine.run
      (config (some skipProgram.initial) (KS.W01.frame old ++ tail) replacement «prefix» scratch [])
      bits = config none tail replacement «prefix» scratch [] := by
  have hs : RunSpec KS.W11.FramedArray.skipProgram
      (KS.W11.FramedArray.«stacks» (KS.W01.frame old ++ tail) replacement «prefix» [])
      (KS.W11.FramedArray.«stacks» tail replacement «prefix» []) (2*old.length+1) := by
    intro bs hb
    erw [KS.W11.FramedArray.skipProgram_run]
    exact (KS.W11.FramedArray.skip_frame old tail replacement «prefix» [] bs hb).1
  have hl : RunSpec skipProgram
      («stacks» (KS.W01.frame old ++ tail) replacement «prefix» scratch [])
      («stacks» tail replacement «prefix» scratch []) (2*old.length+1) := by
    apply KS.W01.FixedPortRunSpec.lift_runSpec _ skipPorts _ _ _ _ _ hs
    · intro j;fin_cases j <;> rfl
    · intro j;fin_cases j <;> rfl
    · intro j hj
      have h0 : j ≠ (0 : Fin 5) := hj 0
      simp [«stacks»,h0]
  exact hl.run_of_le bits hlen

theorem run_reverseNew (src replacement «prefix» bits : List Bool)
    (hlen : replacement.length + 1 ≤ bits.length) :
    reverseNew.toMachine.run
      (config (some reverseNew.initial) src replacement «prefix» [] []) bits =
      config none src [] «prefix» replacement.reverse [] := by
  have h : RunSpec reverseNew («stacks» src replacement «prefix» [] [])
      («stacks» src [] «prefix» replacement.reverse []) (replacement.length+1) := by
    convert KS.W15.RationalMultiply.move_spec (1 : Fin 5) 3 (by decide)
      («stacks» src replacement «prefix» [] []) using 1 <;> (try rfl)
    funext j
    fin_cases j <;> simp [«stacks»,KS.W15.RationalMultiply.moveAfter]
  exact h.run_of_le bits hlen

theorem run_insertNew (src «prefix» reversed bits : List Bool)
    (hlen : reversed.length + 1 ≤ bits.length) :
    insertNew.toMachine.run
      (config (some insertNew.initial) src [] «prefix» reversed []) bits =
      config none (reversed.reverse ++ src) [] «prefix» [] [] := by
  have h : RunSpec insertNew («stacks» src [] «prefix» reversed [])
      («stacks» (reversed.reverse ++ src) [] «prefix» [] []) (reversed.length+1) := by
    convert KS.W15.RationalMultiply.move_spec (3 : Fin 5) 0 (by decide)
      («stacks» src [] «prefix» reversed []) using 1 <;> (try rfl)
    funext j
    fin_cases j <;> simp [«stacks»,KS.W15.RationalMultiply.moveAfter]
  exact h.run_of_le bits hlen

theorem run_restorePrefix (src «prefix» bits : List Bool)
    (hlen : «prefix».length + 1 ≤ bits.length) :
    restorePrefix.toMachine.run
      (config (some restorePrefix.initial) src [] «prefix» [] []) bits =
      config none («prefix».reverse ++ src) [] [] [] [] := by
  have h : RunSpec restorePrefix («stacks» src [] «prefix» [] [])
      («stacks» («prefix».reverse ++ src) [] [] [] []) («prefix».length+1) := by
    convert KS.W15.RationalMultiply.move_spec (2 : Fin 5) 0 (by decide)
      («stacks» src [] «prefix» [] []) using 1 <;> (try rfl)
    funext j
    fin_cases j <;> simp [«stacks»,KS.W15.RationalMultiply.moveAfter]
  exact h.run_of_le bits hlen

theorem run_finish (src replacement «prefix» bits : List Bool)
    (hlen : 2 * replacement.length + «prefix».length + 3 ≤ bits.length) :
    finishProgram.toMachine.run
      (config (some finishProgram.initial) src replacement «prefix» [] []) bits =
      config none («prefix».reverse ++ replacement ++ src) [] [] [] [] := by
  apply run_compose_bounded reverseNew insertAndRestore
    («stacks» src replacement «prefix» [] [])
    («stacks» src [] «prefix» replacement.reverse [])
    («stacks» («prefix».reverse ++ replacement ++ src) [] [] [] [])
    (replacement.length + 1) (replacement.length + «prefix».length + 2)
  · exact run_reverseNew src replacement «prefix»
  · intro bs hb
    apply run_compose_bounded insertNew restorePrefix
      («stacks» src [] «prefix» replacement.reverse [])
      («stacks» (replacement ++ src) [] «prefix» [] [])
      («stacks» («prefix».reverse ++ replacement ++ src) [] [] [] [])
      (replacement.length + 1) («prefix».length + 1)
    · intro cs hc
      have h := run_insertNew src «prefix» replacement.reverse cs (by simpa using hc)
      simp only [List.reverse_reverse] at h ⊢
      exact h
    · intro cs hc
      have h := run_restorePrefix (replacement ++ src) «prefix» cs hc
      simp only [List.append_assoc] at h ⊢
      exact h
    · omega
  · omega

theorem run_replaceTail (old tail replacement «prefix» bits : List Bool)
    (hlen : 2 * old.length + 2 * replacement.length + «prefix».length + 4 ≤ bits.length) :
    replaceTailProgram.toMachine.run
      (config (some replaceTailProgram.initial)
        (KS.W01.frame old ++ tail) replacement «prefix» [] []) bits =
      config none («prefix».reverse ++ replacement ++ tail) [] [] [] [] := by
  apply run_compose_bounded skipProgram finishProgram
    («stacks» (KS.W01.frame old ++ tail) replacement «prefix» [] [])
    («stacks» tail replacement «prefix» [] [])
    («stacks» («prefix».reverse ++ replacement ++ tail) [] [] [] [])
    (2 * old.length + 1) (2 * replacement.length + «prefix».length + 3)
  · exact run_skip old tail replacement «prefix» []
  · exact run_finish tail replacement «prefix»
  · omega

def replaceFuel («prefix» : List (List Bool)) (old new : List Bool) : ℕ :=
  KS.W11.FramedArray.scanFuel «prefix» + 2 * old.length +
    2 * (KS.W01.frame new).length + («prefix».flatMap KS.W01.frame).length + 4

theorem run_replace_prefix («prefix» : List (List Bool)) (old new tail bits : List Bool)
    (hlen : replaceFuel «prefix» old new ≤ bits.length) :
    program.toMachine.run
      (config (some program.initial)
        («prefix».flatMap KS.W01.frame ++ KS.W01.frame old ++ tail)
        (KS.W01.frame new) [] [] (List.replicate «prefix».length true)) bits =
      config none («prefix».flatMap KS.W01.frame ++ KS.W01.frame new ++ tail) [] [] [] [] := by
  apply run_compose_bounded prefixProgram replaceTailProgram
    («stacks» («prefix».flatMap KS.W01.frame ++ KS.W01.frame old ++ tail)
      (KS.W01.frame new) [] [] (List.replicate «prefix».length true))
    («stacks» (KS.W01.frame old ++ tail) (KS.W01.frame new)
      («prefix».flatMap KS.W01.frame).reverse [] [])
    («stacks» («prefix».flatMap KS.W01.frame ++ KS.W01.frame new ++ tail) [] [] [] [])
    (KS.W11.FramedArray.scanFuel «prefix»)
    (2 * old.length + 2 * (KS.W01.frame new).length +
      («prefix».flatMap KS.W01.frame).length + 4)
  · intro bs hb
    have h := run_prefix «prefix»
      (KS.W01.frame old ++ tail) (KS.W01.frame new) bs hb
    simp only [List.append_assoc] at h ⊢
    exact h
  · intro bs hb
    have h := run_replaceTail old tail (KS.W01.frame new) («prefix».flatMap KS.W01.frame).reverse bs
        (by simpa only [List.length_reverse] using hb)
    simp only [List.reverse_reverse] at h ⊢
    exact h
  · unfold replaceFuel at hlen
    omega

theorem replaceFuel_linear («prefix» : List (List Bool)) (old new tail : List Bool) :
    replaceFuel «prefix» old new ≤
      2 * («prefix».flatMap KS.W01.frame ++ KS.W01.frame old ++ tail).length +
        2 * (KS.W01.frame new).length + «prefix».length + 3 := by
  simp only [replaceFuel, KS.W11.FramedArray.scanFuel, List.length_append,
    KS.W01.length_frame]
  omega

theorem run_replace (xs : List (List Bool)) (i : ℕ) (hi : i < xs.length)
    (new tail bits : List Bool)
    (hlen : 2 * (xs.flatMap KS.W01.frame ++ tail).length +
      2 * (KS.W01.frame new).length + i + 3 ≤ bits.length) :
    program.toMachine.run
      (config (some program.initial) (xs.flatMap KS.W01.frame ++ tail)
        (KS.W01.frame new) [] [] (List.replicate i true)) bits =
      config none ((xs.set i new).flatMap KS.W01.frame ++ tail) [] [] [] [] := by
  have hx : xs = xs.take i ++ xs[i] :: xs.drop (i + 1) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have ht : (xs.take i).length = i := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
  have hflat : xs.flatMap KS.W01.frame ++ tail =
      (xs.take i).flatMap KS.W01.frame ++ KS.W01.frame xs[i] ++
        ((xs.drop (i + 1)).flatMap KS.W01.frame ++ tail) := by
    conv_lhs => rw [hx]
    simp only [List.flatMap_append, List.flatMap_cons, List.append_assoc]
  have hset : (xs.set i new).flatMap KS.W01.frame ++ tail =
      (xs.take i).flatMap KS.W01.frame ++ KS.W01.frame new ++
        ((xs.drop (i + 1)).flatMap KS.W01.frame ++ tail) := by
    rw [List.set_eq_take_append_cons_drop, ite_eq_left hi]
    simp only [List.flatMap_append, List.flatMap_cons, List.append_assoc]
  have hb := replaceFuel_linear (xs.take i) xs[i] new
    ((xs.drop (i + 1)).flatMap KS.W01.frame ++ tail)
  rw [← hflat, ht] at hb
  have h := run_replace_prefix (xs.take i) xs[i] new
    ((xs.drop (i + 1)).flatMap KS.W01.frame ++ tail) bits (hb.trans hlen)
  simpa only [← hflat, ← hset, ht] using h

theorem replacement_linear_time (xs : List (List Bool)) (i : ℕ) (hi : i < xs.length)
    (new tail : List Bool) :
    HaltsFromWithin program
      (config (some program.initial) (xs.flatMap KS.W01.frame ++ tail)
        (KS.W01.frame new) [] [] (List.replicate i true))
      (2 * (xs.flatMap KS.W01.frame ++ tail).length + 2 * (KS.W01.frame new).length + i + 3) := by
  intro bits hlen
  exact congrArg (fun c : Config 5 program.states => c.state)
    (run_replace xs i hi new tail bits hlen.ge)

end KS.W11.FramedArrayRewrite

end OAI
