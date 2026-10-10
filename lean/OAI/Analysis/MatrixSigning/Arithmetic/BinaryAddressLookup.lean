import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FixedPortRunSpec
import OAI.Analysis.MatrixSigning.Matrices.MatrixCursorPreparation
import OAI.Analysis.MatrixSigning.Matrices.PreservedMatrixRetrieval

namespace OAI

section

namespace KS.W08

open KS.W01.FixedStack KS.W29.FixedSequential
open KS.W04.ReusableArrayLookup

def matrixCursorPorts : Fin 3 ↪ Fin 5 where
  toFun i := if i = 0 then 1 else if i = 1 then 4 else 3
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

def matrixCursorProgram : Program 5 :=
  ofMachine (KS.W01.FixedStack.liftPorts KS.W03.BinaryToUnary.machine matrixCursorPorts)

private theorem accessConfig_ext {k q : ℕ} {c d : Config k q} (hs : c.state = d.state)
    (ht : ∀ j, c.«stacks» j = d.«stacks» j) : c = d := by
  cases c
  cases d
  exact congrArg₂ Config.mk hs (funext ht)

private theorem ofMachine_lift_run_eq {K : ℕ} (M : Machine)
    (ports : Fin M.stackCount ↪ Fin K) (before after : Fin K → List Bool) (bits : List Bool)
    (h : M.run (projectPorts ports ⟨some M.initial,before⟩) bits=⟨none,fun i=>after (ports i)⟩)
    (hother : ∀ j,(∀ i,j≠ports i)→after j=before j) :
    (ofMachine (KS.W01.FixedStack.liftPorts M ports)).toMachine.run
      ⟨some (ofMachine (KS.W01.FixedStack.liftPorts M ports)).initial,before⟩ bits=⟨none,after⟩ := by
  change (KS.W01.FixedStack.liftPorts M ports).run ⟨some M.initial,before⟩ bits=⟨none,after⟩
  exact KS.W01.FixedStack.liftPorts_run_eq M ports _ bits after h hother

theorem run_matrixCursorProgram {n : ℕ} (M : KS.W07.DenseRatMatrix n) (i j : Fin n)
    (bits : List Bool) (hlen : 8 * n * n + 2 ≤ bits.length) :
    matrixCursorProgram.toMachine.run
      ⟨some matrixCursorProgram.initial,
        arrayStacks (denseMatrixTape M) (denseMatrixBinaryCursor i j) [] [] []⟩ bits =
      ⟨none, arrayStacks (denseMatrixTape M) [] [] [] (denseMatrixCursor i j)⟩ := by
  have hstart : (fun r => arrayStacks (denseMatrixTape M) (denseMatrixBinaryCursor i j)
      [] [] [] (matrixCursorPorts r)) = ![denseMatrixBinaryCursor i j, [], []] := by
    funext r
    fin_cases r <;> rfl
  have hi := (matrixEntryIndex_lt i j).le
  have hl := denseMatrixBinaryCursor_length_le i j
  have hb : 4 * KS.W19.bitsValue (denseMatrixBinaryCursor i j) +
      4 * (denseMatrixBinaryCursor i j).length + 2 ≤ bits.length := by
    rw [denseMatrixBinaryCursor_value]
    nlinarith
  apply ofMachine_lift_run_eq KS.W03.BinaryToUnary.machine matrixCursorPorts
    (arrayStacks (denseMatrixTape M) (denseMatrixBinaryCursor i j) [] [] [])
    (arrayStacks (denseMatrixTape M) [] [] [] (denseMatrixCursor i j)) bits
  · have hp : projectPorts matrixCursorPorts
        (⟨some KS.W03.BinaryToUnary.machine.initial,
          arrayStacks (denseMatrixTape M) (denseMatrixBinaryCursor i j) [] [] []⟩ :
          Config 5 KS.W03.BinaryToUnary.machine.states) =
        KS.W03.BinaryToUnary.machine.init (denseMatrixBinaryCursor i j) := by
      rw [KS.W03.BinaryToUnary.init_eq]
      change Config.mk (some (0 : Fin 8))
        (fun r=>arrayStacks (denseMatrixTape M) (denseMatrixBinaryCursor i j) [] [] [] (matrixCursorPorts r)) =
        Config.mk (some (0 : Fin 8)) ![denseMatrixBinaryCursor i j,[],[]]
      exact congrArg (Config.mk (some (0 : Fin 8))) hstart
    erw [hp,KS.W03.BinaryToUnary.run_input_linear (denseMatrixBinaryCursor i j) bits hb]
    apply congrArg (Config.mk none)
    change ![[],List.replicate (KS.W19.bitsValue (denseMatrixBinaryCursor i j)) true,[]] =
      (fun r=>arrayStacks (denseMatrixTape M) [] [] [] (denseMatrixCursor i j) (matrixCursorPorts r))
    rw [denseMatrixBinaryCursor_value]
    funext r
    fin_cases r <;> rfl
  · intro r hr
    have h1 : r≠1 := hr (0 : Fin 3)
    have h4 : r≠4 := hr (1 : Fin 3)
    have h3 : r≠3 := hr (2 : Fin 3)
    fin_cases r <;> simp_all [arrayStacks]

def binaryMatrixLookupProgram : Program 5 :=
  compose matrixCursorProgram KS.W04.ReusableArrayLookup.program

theorem binaryMatrixLookupProgram_states : binaryMatrixLookupProgram.states = 17 := rfl

theorem run_binaryMatrix_lookup {n : ℕ} (M : KS.W07.DenseRatMatrix n) (b : ℕ)
    (hnum : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).den ≤ 2 ^ b)
    (i j : Fin n) (bits : List Bool)
    (hlen : n * n * (40 * b + 84) + 6 ≤ bits.length) :
    binaryMatrixLookupProgram.toMachine.run
      ⟨some binaryMatrixLookupProgram.initial,
        arrayStacks (denseMatrixTape M) (denseMatrixBinaryCursor i j) [] [] []⟩ bits =
      ⟨none, arrayStacks (denseMatrixTape M) []
        (KS.W01.encodeRat (AccessCounted.readMatrix M i j).value) [] []⟩ := by
  apply run_compose_bounded matrixCursorProgram KS.W04.ReusableArrayLookup.program
    (arrayStacks (denseMatrixTape M) (denseMatrixBinaryCursor i j) [] [] [])
    (arrayStacks (denseMatrixTape M) [] [] [] (denseMatrixCursor i j))
    (arrayStacks (denseMatrixTape M) []
      (KS.W01.encodeRat (AccessCounted.readMatrix M i j).value) [] [])
    (8 * n * n + 2) (n * n * (40 * b + 76) + 4)
  · exact run_matrixCursorProgram M i j
  · intro coins hc
    have ht := denseMatrixTape_length_le M b hnum hden
    have hi := (matrixEntryIndex_lt i j).le
    have hb : 5 * (denseMatrixTape M ++ []).length + i.val * n + j.val + 4 ≤
        coins.length := by
      rw [List.append_nil]
      have he : 5 * (n * n * (8 * b + 15)) + n * n + 4 =
          n * n * (40 * b + 76) + 4 := by ring
      nlinarith
    simpa only [List.append_nil] using run_preservedMatrix_lookup M i j [] coins hb
  · have he : (8 * n * n + 2) + (n * n * (40 * b + 76) + 4) =
        n * n * (40 * b + 84) + 6 := by ring
    simpa only [he] using hlen

theorem binaryMatrix_lookup_time {n : ℕ} (M : KS.W07.DenseRatMatrix n) (b : ℕ)
    (hnum : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (KS.W07.DenseRatMatrix.decode M i j).den ≤ 2 ^ b)
    (i j : Fin n) :
    HaltsFromWithin binaryMatrixLookupProgram
      ⟨some binaryMatrixLookupProgram.initial,
        arrayStacks (denseMatrixTape M) (denseMatrixBinaryCursor i j) [] [] []⟩
      (n * n * (40 * b + 84) + 6) := by
  intro bits hlen
  exact congrArg Config.state (run_binaryMatrix_lookup M b hnum hden i j bits hlen.ge)

end KS.W08

end

end OAI
