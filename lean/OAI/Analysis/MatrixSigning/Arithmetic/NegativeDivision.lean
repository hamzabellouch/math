import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.RationalDivisionMachine
import OAI.Analysis.MatrixSigning.Arithmetic.ZeroPaddedRow

namespace OAI

namespace KS.W12.RowDot
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def divisionPorts : Fin 15 ↪ Fin 29 := Fin.castLEEmb (by decide)
def divisionProgram : Program 29 := KS.W29.FixedSequential.liftPorts KS.W30.RationalDivision.program divisionPorts

def arithmeticState (saved : Fin 29 → List Bool) (input output : List Bool) : Fin 29 → List Bool :=
  fun j => if j = 0 then input else if j = 10 then output else if j.val < 19 then [] else saved j

theorem division_spec (saved : Fin 29 → List Bool) (q r : ℚ) :
    RunSpec divisionProgram (arithmeticState saved (KS.W01.encodeRat q ++ KS.W01.encodeRat r) [])
      (arithmeticState saved [] (KS.W01.encodeRat (q / r))) (KS.W30.RationalDivision.totalTicks q r) := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec _ _ _ _ _ _ _ (KS.W30.RationalDivision.full_spec q r)
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases j <;> rfl
  · intro j hj
    have h0 : j ≠ 0 := hj 0
    have h10 : j ≠ 10 := hj 10
    simp [arithmeticState, h0, h10]

def minusOneProgram : Program 29 := compose (compose (compose (compose
  (literalPush 0 true) (literalPush 0 true)) (literalPush 0 false))
  (literalPush 0 true)) (literalPush 0 true)

theorem minusOne_spec (s : Fin 29 → List Bool) :
    RunSpec minusOneProgram s (put s 0 (KS.W01.encodeRat (-1) ++ s 0)) 5 := by
  let s1 := put s 0 (true :: s 0)
  let s2 := put s1 0 (true :: s1 0)
  let s3 := put s2 0 (false :: s2 0)
  let s4 := put s3 0 (true :: s3 0)
  have h := ((((literalPush_spec (0 : Fin 29) true s).compose
    (literalPush_spec 0 true s1)).compose (literalPush_spec 0 false s2)).compose
    (literalPush_spec 0 true s3)).compose (literalPush_spec 0 true s4)
  have he : KS.W01.encodeRat (-1) = [true, true, false, true, true] := by decide
  convert h using 1 <;> (try rfl)
  funext j
  by_cases hj : j = 0 <;> simp [s1, s2, s3, s4, put, hj, he]

def productPorts : Fin 13 ↪ Fin 29 := Fin.castLEEmb (by decide)
def productProgram : Program 29 := KS.W29.FixedSequential.liftPorts KS.W15.RationalMultiply.program productPorts

theorem product_spec (saved : Fin 29 → List Bool) (q r : ℚ) :
    RunSpec productProgram (arithmeticState saved (KS.W01.encodeRat q ++ KS.W01.encodeRat r) [])
      (arithmeticState saved [] (KS.W01.encodeRat (q * r))) (KS.W15.RationalMultiply.totalTicks q r) := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec _ _ _ _ _ _ _ (KS.W15.RationalMultiply.full_spec q r)
  · intro j; fin_cases j <;> rfl
  · intro j; fin_cases j <;> rfl
  · intro j hj
    have h0 : j ≠ 0 := hj 0
    have h10 : j ≠ 10 := hj 10
    simp [arithmeticState, h0, h10]

def negativeDivisionProgram : Program 29 := compose (compose (compose divisionProgram minusOneProgram)
  (StackTransfer.program 10 0 26)) productProgram

def negativeDivisionTicks (q r : ℚ) : ℕ := KS.W30.RationalDivision.totalTicks q r + 5 +
  (2 * (KS.W01.encodeRat (q / r)).length + 2) + KS.W15.RationalMultiply.totalTicks (q / r) (-1)

theorem negativeDivision_spec (saved : Fin 29 → List Bool) (q r : ℚ) (hs : saved 26 = []) :
    RunSpec negativeDivisionProgram
      (arithmeticState saved (KS.W01.encodeRat q ++ KS.W01.encodeRat r) [])
      (arithmeticState saved [] (KS.W01.encodeRat (-(q / r)))) (negativeDivisionTicks q r) := by
  let s := arithmeticState saved [] (KS.W01.encodeRat (q / r))
  let t := put s 0 (KS.W01.encodeRat (-1))
  have h1 := division_spec saved q r
  have h2 : RunSpec minusOneProgram s t 5 := by simpa [s, t, arithmeticState] using minusOne_spec s
  have h3 : RunSpec (StackTransfer.program 10 0 26) t
      (arithmeticState saved (KS.W01.encodeRat (q / r) ++ KS.W01.encodeRat (-1)) [])
      (2 * (KS.W01.encodeRat (q / r)).length + 2) := by
    convert StackTransfer.spec (10 : Fin 29) 0 26 (by decide) (by decide) (by decide) t
      (by simp [t, s, put, arithmeticState, hs]) using 1 <;> (try rfl)
    funext j
    fin_cases j <;> simp [StackTransfer.after, t, s, put, arithmeticState]
  have h4 := product_spec saved (q / r) (-1)
  have h := ((h1.compose h2).compose h3).compose h4
  simpa [negativeDivisionProgram, negativeDivisionTicks] using h

theorem negativeDivisionTicks_le (q r : ℚ) :
    negativeDivisionTicks q r ≤ KS.W29.polynomialFuel 100000000 3
      (KS.W01.encodeRat q ++ KS.W01.encodeRat r).length := by
  let N := KS.W01.ratLength q + KS.W01.ratLength r + 1
  have hN : 0 < N := by dsimp [N]; omega
  have hd := KS.W30.RationalDivision.totalTicks_le_polynomial q r
  have hq := KS.W01.ratLength_div_le q r
  have hm := KS.W15.RationalMultiply.totalTicks_le_polynomial (q / r) (-1)
  have hminus : KS.W01.ratLength (-1) = 5 := by decide
  have hpair : (KS.W15.RationalMultiply.inputBits (q / r) (-1)).length + 1 ≤ 13 * N := by
    simp only [KS.W15.RationalMultiply.inputBits, List.length_append]
    change KS.W01.ratLength (q / r) + KS.W01.ratLength (-1) + 1 ≤ 13 * N
    rw [hminus]
    dsimp [N]
    omega
  have hm' : KS.W15.RationalMultiply.totalTicks (q / r) (-1) ≤ 4499456 * N ^ 3 := by
    calc
      _ ≤ 2048 * ((KS.W15.RationalMultiply.inputBits (q / r) (-1)).length + 1) ^ 3 := hm
      _ ≤ 2048 * (13 * N) ^ 3 := by gcongr
      _ = _ := by ring
  have hl : N ≤ N ^ 3 := Nat.le_self_pow (by decide) N
  change negativeDivisionTicks q r ≤ 100000000 * ((KS.W01.encodeRat q ++ KS.W01.encodeRat r).length + 1) ^ 3
  simp only [List.length_append]
  change negativeDivisionTicks q r ≤ 100000000 * N ^ 3
  unfold negativeDivisionTicks
  change KS.W30.RationalDivision.totalTicks q r + 5 + (2 * KS.W01.ratLength (q / r) + 2) +
    KS.W15.RationalMultiply.totalTicks (q / r) (-1) ≤ _
  simp only [KS.W29.polynomialFuel, KS.W30.RationalDivision.inputBits,
    List.length_append] at hd
  change KS.W30.RationalDivision.totalTicks q r ≤ 1100000 * N ^ 3 at hd
  dsimp [N] at *
  omega

end KS.W12.RowDot

end OAI
