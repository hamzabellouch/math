import Mathlib
import OAI.Analysis.MatrixSigning.Optimization.SchurWitnessHead

namespace OAI

namespace KS.W12.StoredWitnessLift
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators KS.W07
open KS.W12.RowDot

def saved {n : ℕ} (M : DenseRatMatrix (n + 1)) (y : Fin n → ℚ) : Fin 30 → List Bool :=
  fun j => if j = 19 then KS.W08.denseMatrixTape M else if j = 22 then Computability.encodeNat (n + 1)
    else if j = 29 then vectorTape y else []

def work {n : ℕ} (M : DenseRatMatrix (n + 1)) (y : Fin n → ℚ)
    (padded head result : List Bool) : Fin 30 → List Bool :=
  fun j => if j = 20 then padded else if j = 10 then head else if j = 17 then result else saved M y j

def padPorts : Fin 3 ↪ Fin 30 := ⟨![29, 20, 26], by decide⟩
def headPorts : Fin 29 ↪ Fin 30 := Fin.castLEEmb (by decide)
def copyPorts : Fin 3 ↪ Fin 30 := ⟨![29, 17, 26], by decide⟩
def framePorts : Fin 3 ↪ Fin 30 := ⟨![4, 10, 26], by decide⟩
def headProgram : Program 30 := KS.W29.FixedSequential.liftPorts schurHeadProgram headPorts

def program : Program 30 := compose (compose (compose (compose (compose
  (copyZeroPadded padPorts) headProgram) (KS.W11.FrameWireCodec.frameProgram framePorts))
  (KS.W01.FixedCopy.program copyPorts)) (KS.W12.StackTransfer.program 10 17 26))
  (KS.W04.BinaryStackMoves.clearProgram 20)

def headBudget {n : ℕ} (M : DenseRatMatrix (n + 1)) (y : Fin n → ℚ) : ℕ :=
  KS.W29.polynomialFuel 10000000000000000 8 (storedLength M (zeroPadded y) 0)

def ticks {n : ℕ} (M : DenseRatMatrix (n + 1)) (y : Fin n → ℚ) : ℕ :=
  (2 * (vectorTape y).length + 13) + headBudget M y +
  (4 * (KS.W01.encodeRat (schurHead M y)).length + 3) +
  (2 * (vectorTape y).length + 2) +
  (2 * (KS.W01.frame (KS.W01.encodeRat (schurHead M y))).length + 2) +
  ((vectorTape (zeroPadded y)).length + 1)

theorem full_spec {n : ℕ} (M : DenseRatMatrix (n + 1)) (y : Fin n → ℚ) :
    RunSpec program (saved M y)
      (Function.update (saved M y) 17 (vectorTape (Fin.cons (schurHead M y) y))) (ticks M y) := by
  let z := KS.W01.encodeRat (schurHead M y)
  let padded := vectorTape (zeroPadded y)
  have h1 : RunSpec (copyZeroPadded padPorts) (saved M y) (work M y padded [] [])
      (2 * (vectorTape y).length + 13) := by
    convert copyZeroPadded_spec padPorts (saved M y) y rfl rfl rfl using 1
    funext j
    fin_cases j <;> rfl
  have h2 : RunSpec headProgram (work M y padded [] []) (work M y padded z []) (headBudget M y) := by
    apply KS.W01.FixedPortRunSpec.lift_runSpec _ _ _ _ _ _ _ (schurHead_polynomial_spec M y)
    · intro j
      fin_cases j <;> rfl
    · intro j
      fin_cases j <;> rfl
    · intro j hj
      have h10 : j ≠ 10 := hj 10
      simp [work, h10]
  have h3 : RunSpec (KS.W11.FrameWireCodec.frameProgram framePorts) (work M y padded z [])
      (work M y padded (KS.W01.frame z) []) (4 * z.length + 3) := by
    convert KS.W11.FrameWireCodec.frame_spec framePorts (work M y padded z []) z using 1 <;>
      funext j <;> fin_cases j <;>
      simp [work, saved, framePorts, KS.W28.FixedPositiveSerializer.registers]
  have h4 : RunSpec (KS.W01.FixedCopy.program copyPorts) (work M y padded (KS.W01.frame z) [])
      (work M y padded (KS.W01.frame z) (vectorTape y)) (2 * (vectorTape y).length + 2) := by
    intro bits hbits
    have h := KS.W01.FixedCopy.run_copy_restore copyPorts (work M y padded (KS.W01.frame z) [])
      (vectorTape y) bits rfl rfl rfl hbits
    refine (KS.W19.MachineTransport.run_ofMachine
      (KS.W01.FixedCopy.machine copyPorts)
      (⟨some (0 : Fin 2), work M y padded (KS.W01.frame z) []⟩ : Config 30 2)
      bits).trans (h.trans ?_)
    apply congrArg (fun ws : Fin 30 → List Bool =>
      (Config.mk (none : Option (Fin 2)) ws : Config 30 2))
    funext j
    fin_cases j <;> rfl
  have h5 : RunSpec (KS.W12.StackTransfer.program 10 17 26)
      (work M y padded (KS.W01.frame z) (vectorTape y))
      (work M y padded [] (KS.W01.frame z ++ vectorTape y))
      (2 * (KS.W01.frame z).length + 2) := by
    convert KS.W12.StackTransfer.spec (10 : Fin 30) 17 26 (by decide) (by decide) (by decide)
      (work M y padded (KS.W01.frame z) (vectorTape y)) rfl using 1 <;> (try rfl)
    funext j
    fin_cases j <;> simp [KS.W12.StackTransfer.after, work, saved]
  have h6 : RunSpec (KS.W04.BinaryStackMoves.clearProgram 20)
      (work M y padded [] (KS.W01.frame z ++ vectorTape y))
      (Function.update (saved M y) 17 (vectorTape (Fin.cons (schurHead M y) y)))
      (padded.length + 1) := by
    convert KS.W15.RationalMultiply.clear_spec (20 : Fin 30)
      (work M y padded [] (KS.W01.frame z ++ vectorTape y)) using 1 <;> (try rfl)
    funext j
    fin_cases j <;> simp [KS.W15.RationalMultiply.clearAfter, work, saved, vectorTape_cons, z]
  exact ((((h1.compose h2).compose h3).compose h4).compose h5).compose h6

def inputLength {n : ℕ} (M : DenseRatMatrix (n + 1)) (y : Fin n → ℚ) : ℕ :=
  (KS.W08.denseMatrixTape M).length + (Computability.encodeNat (n + 1)).length + (vectorTape y).length

theorem headBudget_le {n : ℕ} (M : DenseRatMatrix (n + 1)) (y : Fin n → ℚ) :
    headBudget M y ≤ 4299816960000000000000000 * (inputLength M y + 1) ^ 8 := by
  have hzero : (KS.W01.frame (KS.W01.encodeRat 0)).length = 11 := by decide
  have hdimZero : Computability.encodeNat 0 = [] := rfl
  have hlen : storedLength M (zeroPadded y) 0 = inputLength M y + 11 := by
    simp [storedLength, inputLength, zeroPadded, vectorTape_cons,
      List.length_append, hzero, hdimZero,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  unfold headBudget KS.W29.polynomialFuel
  rw [hlen]
  calc
    _ ≤ 10000000000000000 * (12 * (inputLength M y + 1)) ^ 8 :=
      Nat.mul_le_mul_left 10000000000000000 (Nat.pow_le_pow_left
        (show inputLength M y + 11 + 1 ≤ 12 * (inputLength M y + 1) by omega) 8)
    _ = _ := by ring

private theorem runSpec_stack_length_le {k : ℕ} (P : Program k)
    (before after : Fin k → List Bool) (budget : ℕ)
    (hP : RunSpec P before after budget) (j : Fin k) :
    (after j).length ≤ (before j).length + budget := by
  let bs := List.replicate budget false
  have hexec := hP bs (by simp [bs])
  have h := P.toMachine.run_stack_length_le
    (⟨some P.initial, before⟩ : Config k P.states) bs j
  have hout := congrArg (fun c : Config k P.states => (c.«stacks» j).length) hexec
  have hfinal := hout.symm.trans_le h
  simpa only [bs, List.length_replicate] using hfinal

theorem head_length_le_budget {n : ℕ} (M : DenseRatMatrix (n + 1)) (y : Fin n → ℚ) :
    (KS.W01.encodeRat (schurHead M y)).length ≤ headBudget M y := by
  have h := runSpec_stack_length_le schurHeadProgram
    (initialStacks M (zeroPadded y) 0)
    (put (initialStacks M (zeroPadded y) 0) 10 (KS.W01.encodeRat (schurHead M y)))
    (headBudget M y) (schurHead_polynomial_spec M y) (10 : Fin 29)
  change (KS.W01.encodeRat (schurHead M y)).length ≤ ([] : List Bool).length + headBudget M y at h
  simpa only [List.length_nil, Nat.zero_add] using h

theorem ticks_polynomial {n : ℕ} (M : DenseRatMatrix (n + 1)) (y : Fin n → ℚ) :
    ticks M y ≤ KS.W29.polynomialFuel 10000000000000000000000000000 8 (inputLength M y) := by
  have hh := head_length_le_budget M y
  have hb := headBudget_le M y
  have ht : (vectorTape y).length ≤ inputLength M y := by unfold inputLength; omega
  have hzero : (KS.W01.frame (KS.W01.encodeRat 0)).length = 11 := by decide
  have hp : (vectorTape (zeroPadded y)).length = 11 + (vectorTape y).length := by
    simp only [zeroPadded, vectorTape_cons, List.length_append, hzero]
  have hgrow : inputLength M y + 1 ≤ (inputLength M y + 1) ^ 8 := by
    simpa only [pow_one] using (Nat.pow_le_pow_right (n := inputLength M y + 1) (by omega)
      (show 1 ≤ 8 by decide))
  unfold ticks KS.W29.polynomialFuel
  rw [hp, KS.W01.length_frame]
  omega

theorem polynomial_spec {n : ℕ} (M : DenseRatMatrix (n + 1)) (y : Fin n → ℚ) :
    RunSpec program (saved M y)
      (Function.update (saved M y) 17 (vectorTape (Fin.cons (schurHead M y) y)))
      (KS.W29.polynomialFuel 10000000000000000000000000000 8 (inputLength M y)) :=
  (full_spec M y).mono (ticks_polynomial M y)

end KS.W12.StoredWitnessLift

end OAI
