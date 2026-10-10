import Mathlib
import OAI.Analysis.MatrixSigning.Matrices.RowDotBounds

namespace OAI

namespace KS.W12.RowDot
open Matrix
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07
open scoped BigOperators

def literalDispatch {k : ℕ} (port : Fin k) (b : Bool) (_ : Fin 1)
    (_heads : Fin k → Fin 3) (_coin : Bool) : Instruction k 1 :=
  ⟨none, Vector.ofFn (fun j => if j = port then .push b else .stay)⟩
def literalPush {k : ℕ} (port : Fin k) (b : Bool) : Program k :=
  ofMachine (compile 0 port port (literalDispatch port b))

theorem literalPush_spec {k : ℕ} (port : Fin k) (b : Bool) (s : Fin k → List Bool) :
    RunSpec (literalPush port b) s (Function.update s port (b :: s port)) 1 := by
  intro bits hbits
  cases bits with
  | nil => simp at hbits
  | cons coin rest =>
      have hr : rest = [] := by simpa using hbits
      subst rest
      refine (KS.W19.MachineTransport.run_ofMachine
        (compile (0 : Fin 1) port port (literalDispatch port b))
        (⟨some (0 : Fin 1), s⟩ : Config k 1) [coin]).trans ?_
      simp only [Machine.run]
      refine (step_compile (0 : Fin 1) port port (literalDispatch port b)
        (0 : Fin 1) s coin).trans ?_
      change (Config.mk (none : Option (Fin 1)) _ : Config k 1) = Config.mk none _
      apply congrArg (fun ws : Fin k → List Bool =>
        (Config.mk (none : Option (Fin 1)) ws : Config k 1))
      funext j
      by_cases hj : j = port
      · subst j
        simp [literalDispatch, Instruction.action, KS.W29.StackAction.apply]
      · simp [literalDispatch, Instruction.action, KS.W29.StackAction.apply, hj]

def zeroFrame : List Bool := KS.W01.frame (KS.W01.encodeRat 0)

def prependZero {k : ℕ} (port : Fin k) : Program k :=
  compose (compose (compose (compose (compose (compose (compose (compose (compose (compose
    (literalPush port true) (literalPush port true)) (literalPush port false))
    (literalPush port true)) (literalPush port false)) (literalPush port false))
    (literalPush port false)) (literalPush port true)) (literalPush port false))
    (literalPush port false)) (literalPush port false)

theorem prependZero_spec {k : ℕ} (port : Fin k) (s : Fin k → List Bool) :
    RunSpec (prependZero port) s (Function.update s port (zeroFrame ++ s port)) 11 := by
  let s1 := Function.update s port (true :: s port)
  let s2 := Function.update s1 port (true :: s1 port)
  let s3 := Function.update s2 port (false :: s2 port)
  let s4 := Function.update s3 port (true :: s3 port)
  let s5 := Function.update s4 port (false :: s4 port)
  let s6 := Function.update s5 port (false :: s5 port)
  let s7 := Function.update s6 port (false :: s6 port)
  let s8 := Function.update s7 port (true :: s7 port)
  let s9 := Function.update s8 port (false :: s8 port)
  let s10 := Function.update s9 port (false :: s9 port)
  have h := ((((((((((literalPush_spec port true s).compose (literalPush_spec port true s1)).compose
    (literalPush_spec port false s2)).compose (literalPush_spec port true s3)).compose
    (literalPush_spec port false s4)).compose (literalPush_spec port false s5)).compose
    (literalPush_spec port false s6)).compose (literalPush_spec port true s7)).compose
    (literalPush_spec port false s8)).compose (literalPush_spec port false s9)).compose
    (literalPush_spec port false s10)
  have hz : zeroFrame = [false, false, false, true, false, false, false, true, false, true, true] := by decide
  convert h using 1 <;> (try rfl)
  funext j
  by_cases hj : j = port <;>
    simp [hz, hj, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10]

theorem vectorTape_cons {n : ℕ} (a : ℚ) (y : Fin n → ℚ) :
    vectorTape (Fin.cons a y) = KS.W01.frame (KS.W01.encodeRat a) ++ vectorTape y := by
  simp [vectorTape, List.ofFn_succ]

def zeroPadded {n : ℕ} (y : Fin n → ℚ) : Fin (n + 1) → ℚ := Fin.cons 0 y

def copyZeroPadded {k : ℕ} (ports : Fin 3 ↪ Fin k) : Program k :=
  compose (KS.W01.FixedCopy.program ports) (prependZero (ports 1))

theorem copyZeroPadded_spec {k n : ℕ} (ports : Fin 3 ↪ Fin k) (s : Fin k → List Bool)
    (y : Fin n → ℚ) (hs : s (ports 0) = vectorTape y)
    (hd : s (ports 1) = []) (ht : s (ports 2) = []) :
    RunSpec (copyZeroPadded ports) s
      (Function.update s (ports 1) (vectorTape (zeroPadded y)))
      (2 * (vectorTape y).length + 13) := by
  have hc : RunSpec (KS.W01.FixedCopy.program ports) s
      (Function.update s (ports 1) (vectorTape y)) (2 * (vectorTape y).length + 2) := by
    intro bits hbits
    exact KS.W01.FixedCopy.run_copy_restore ports s (vectorTape y) bits hs hd ht hbits
  have h := hc.compose (prependZero_spec (ports 1) (Function.update s (ports 1) (vectorTape y)))
  simpa [copyZeroPadded, zeroPadded, vectorTape_cons, zeroFrame, Function.update_idem,
    Nat.add_assoc] using h

theorem zeroPadded_row_dot {n : ℕ} (M : DenseRatMatrix (n + 1)) (y : Fin n → ℚ) :
    (DenseRatMatrix.decode M *ᵥ zeroPadded y) 0 =
      ∑ j : Fin n, DenseRatMatrix.decode M 0 j.succ * y j := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, zeroPadded]

theorem zeroPadded_polynomial_spec {n : ℕ} (M : DenseRatMatrix (n + 1)) (y : Fin n → ℚ) :
    RunSpec program (initialStacks M (zeroPadded y) 0)
      (put (initialStacks M (zeroPadded y) 0) 17
        (KS.W01.encodeRat (∑ j : Fin n, DenseRatMatrix.decode M 0 j.succ * y j)))
      (KS.W29.polynomialFuel 1000000000000 8 (storedLength M (zeroPadded y) 0)) := by
  simpa only [zeroPadded_row_dot] using polynomial_spec M (zeroPadded y) 0

end KS.W12.RowDot

end OAI
