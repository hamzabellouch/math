import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.RationalAddModel
import OAI.Analysis.MatrixSigning.Arithmetic.RationalAddProducts
import OAI.Analysis.MatrixSigning.Arithmetic.FixedSubtraction

namespace OAI

namespace KS.W13.RationalAdd
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W15.RationalMultiply (move_spec moveAfter clear_spec clearAfter)
open KS.W06.RationalCompare (sign_spec signAfter signProgram branch_spec_left branch_spec_right)
open KS.W19.UnsignedPairSerializer (registers)

def readyState (s : Bool) (num den : List Bool) : Fin 16 → List Bool :=
  extend (KS.W30.RationalMagnitudeMachine.state num den s) [] [] []

def numeratorAt (sa sb : Bool) (loc : Fin 16) (num den : List Bool) : Fin 16 → List Bool :=
  fun j => if j = loc then num else signedState sa [] sb [] den j

def finishNumeratorProgram (loc signPort : Fin 16) : Program 16 :=
  compose (compose (compose (compose (compose (compose
    (KS.W04.BinaryStackMoves.moveProgram loc 0)
    (KS.W04.BinaryStackMoves.moveProgram 0 10))
    (signProgram signPort 12))
    (KS.W04.BinaryStackMoves.clearProgram 1))
    (KS.W04.BinaryStackMoves.clearProgram 4))
    (KS.W04.BinaryStackMoves.moveProgram 15 0))
    (KS.W04.BinaryStackMoves.moveProgram 0 11)

theorem finishNumerator_spec (sa sb : Bool) (loc signPort : Fin 16) (num den : List Bool)
    (hloc : loc = 7 ∨ loc = 8) (hsp : signPort = 1 ∨ signPort = 4) :
    RunSpec (finishNumeratorProgram loc signPort) (numeratorAt sa sb loc num den)
      (readyState (if signPort = 1 then sa else sb) num den)
      (2 * num.length + 2 * den.length + 8) := by
  let chosen := if signPort = 1 then sa else sb
  have h1 := move_spec loc (0 : Fin 16) (by rcases hloc with rfl | rfl <;> decide)
    (numeratorAt sa sb loc num den)
  have h2 := move_spec (0 : Fin 16) 10 (by decide)
    (moveAfter loc 0 (numeratorAt sa sb loc num den))
  have h3 := sign_spec signPort (12 : Fin 16) (by rcases hsp with rfl | rfl <;> decide)
    (moveAfter 0 10 (moveAfter loc 0 (numeratorAt sa sb loc num den))) chosen []
    (by rcases hloc with rfl | rfl <;> rcases hsp with rfl | rfl <;> rfl)
  have h4 := clear_spec (1 : Fin 16) (signAfter signPort 12
    (moveAfter 0 10 (moveAfter loc 0 (numeratorAt sa sb loc num den))) chosen [])
  have h5 := clear_spec (4 : Fin 16) (clearAfter 1 (signAfter signPort 12
    (moveAfter 0 10 (moveAfter loc 0 (numeratorAt sa sb loc num den))) chosen []))
  have h6 := move_spec (15 : Fin 16) 0 (by decide) (clearAfter 4 (clearAfter 1 (signAfter signPort 12
    (moveAfter 0 10 (moveAfter loc 0 (numeratorAt sa sb loc num den))) chosen [])))
  have h7 := move_spec (0 : Fin 16) 11 (by decide) (moveAfter 15 0
    (clearAfter 4 (clearAfter 1 (signAfter signPort 12
      (moveAfter 0 10 (moveAfter loc 0 (numeratorAt sa sb loc num den))) chosen []))))
  have h := (((((h1.compose h2).compose h3).compose h4).compose h5).compose h6).compose h7
  rcases hloc with rfl | rfl <;> rcases hsp with rfl | rfl
  all_goals
    convert h using 1 <;>
      first
      | rfl
      | (funext j; fin_cases j <;> simp [chosen, numeratorAt, signedState, readyState, extend,
          KS.W30.RationalMagnitudeMachine.state, KS.W30.RationalMagnitudeMachine.«stacks», moveAfter, clearAfter, signAfter])
      | (simp [numeratorAt, signedState, moveAfter, clearAfter, signAfter]; omega)

def addPorts : Fin 3 ↪ Fin 16 := ⟨![7,8,9], by decide⟩
def rightSubtractPorts : Fin 3 ↪ Fin 16 := ⟨![8,7,9], by decide⟩
def equalProgram : Program 16 := compose (canonicalAddProgram addPorts) (finishNumeratorProgram 8 1)
def leftLargeProgram : Program 16 := compose (KS.W19.FixedSubtraction.program addPorts) (finishNumeratorProgram 8 1)
def rightLargeProgram : Program 16 := compose (KS.W19.FixedSubtraction.program rightSubtractPorts) (finishNumeratorProgram 7 4)

def arithmeticBudget (xs ys den : List Bool) : ℕ := 16 * (xs.length + ys.length + den.length + 1)

theorem equal_spec (sa sb : Bool) (xs ys den : List Bool) :
    RunSpec equalProgram (signedState sa xs sb ys den) (readyState sa (addResult xs ys) den)
      (arithmeticBudget xs ys den) := by
  have ha : RunSpec (canonicalAddProgram addPorts) (signedState sa xs sb ys den)
      (numeratorAt sa sb 8 (addResult xs ys) den) (canonicalAddTicks xs ys) := by
    convert canonicalAdd_spec addPorts (signedState sa xs sb ys den) xs ys using 1 <;>
      first | rfl | (funext j; fin_cases j <;> rfl)
  have hf := finishNumerator_spec sa sb 8 1 (addResult xs ys) den (Or.inr rfl) (Or.inl rfl)
  apply (ha.compose hf).mono
  have ht := canonicalAddTicks_le xs ys
  have hl := addResult_length_le xs ys
  unfold arithmeticBudget
  omega

theorem leftLarge_spec (sa sb : Bool) (xs ys den : List Bool)
    (horder : KS.W19.bitsValue ys ≤ KS.W19.bitsValue xs) :
    RunSpec leftLargeProgram (signedState sa xs sb ys den)
      (readyState sa (Computability.encodeNat (KS.W19.bitsValue xs - KS.W19.bitsValue ys)) den)
      (arithmeticBudget xs ys den) := by
  let num := Computability.encodeNat (KS.W19.bitsValue xs - KS.W19.bitsValue ys)
  have hs : RunSpec (KS.W19.FixedSubtraction.program addPorts) (signedState sa xs sb ys den)
      (numeratorAt sa sb 8 num den) (2 * (max xs.length ys.length + 1)) := by
    convert KS.W19.FixedSubtraction.subtract_spec addPorts (signedState sa xs sb ys den) xs ys horder using 1 <;>
      first | rfl | (funext j; fin_cases j <;> rfl)
  have hf := finishNumerator_spec sa sb 8 1 num den (Or.inr rfl) (Or.inl rfl)
  apply (hs.compose hf).mono
  have hl := subtractResult_length_le xs ys horder
  unfold arithmeticBudget
  dsimp [num] at *
  omega

theorem rightLarge_spec (sa sb : Bool) (xs ys den : List Bool)
    (horder : KS.W19.bitsValue xs ≤ KS.W19.bitsValue ys) :
    RunSpec rightLargeProgram (signedState sa xs sb ys den)
      (readyState sb (Computability.encodeNat (KS.W19.bitsValue ys - KS.W19.bitsValue xs)) den)
      (arithmeticBudget xs ys den) := by
  let num := Computability.encodeNat (KS.W19.bitsValue ys - KS.W19.bitsValue xs)
  have hs : RunSpec (KS.W19.FixedSubtraction.program rightSubtractPorts) (signedState sa xs sb ys den)
      (numeratorAt sa sb 7 num den) (2 * (max ys.length xs.length + 1)) := by
    convert KS.W19.FixedSubtraction.subtract_spec rightSubtractPorts (signedState sa xs sb ys den) ys xs horder using 1 <;>
      first | rfl | (funext j; fin_cases j <;> rfl)
  have hf := finishNumerator_spec sa sb 7 4 num den (Or.inl rfl) (Or.inr rfl)
  apply (hs.compose hf).mono
  have hl := subtractResult_length_le ys xs horder
  unfold arithmeticBudget
  dsimp [num] at *
  omega

def compareLeftCopyPorts : Fin 3 ↪ Fin 16 := ⟨![7,10,9], by decide⟩
def compareRightCopyPorts : Fin 3 ↪ Fin 16 := ⟨![8,11,9], by decide⟩
def comparePorts : Fin 3 ↪ Fin 16 := ⟨![10,11,12], by decide⟩
def copyCompareProgram : Program 16 := compose
  (compose (KS.W01.FixedCopy.program compareLeftCopyPorts) (KS.W01.FixedCopy.program compareRightCopyPorts))
  (KS.W28.FixedCompare.program comparePorts)

def comparedState (sa : Bool) (xs : List Bool) (sb : Bool) (ys den : List Bool) : Fin 16 → List Bool :=
  Function.update (signedState sa xs sb ys den) 12 [decide (KS.W19.bitsValue xs ≤ KS.W19.bitsValue ys)]

theorem copyCompare_spec (sa sb : Bool) (xs ys den : List Bool) :
    RunSpec copyCompareProgram (signedState sa xs sb ys den) (comparedState sa xs sb ys den)
      (3 * xs.length + 3 * ys.length + 5) := by
  let middle := Function.update (signedState sa xs sb ys den) 10 xs
  let copied := Function.update middle 11 ys
  have hl : RunSpec (KS.W01.FixedCopy.program compareLeftCopyPorts)
      (signedState sa xs sb ys den) middle (2 * xs.length + 2) := by
    apply KS.W03.MachineRoundTrip.runSpec_ofMachine (KS.W01.FixedCopy.machine compareLeftCopyPorts)
    intro bits hb
    exact KS.W01.FixedCopy.run_copy_restore compareLeftCopyPorts _ xs bits rfl rfl rfl hb
  have hr : RunSpec (KS.W01.FixedCopy.program compareRightCopyPorts)
      middle copied (2 * ys.length + 2) := by
    apply KS.W03.MachineRoundTrip.runSpec_ofMachine (KS.W01.FixedCopy.machine compareRightCopyPorts)
    intro bits hb
    exact KS.W01.FixedCopy.run_copy_restore compareRightCopyPorts _ ys bits rfl rfl rfl hb
  have hc : RunSpec (KS.W28.FixedCompare.program comparePorts) copied
      (comparedState sa xs sb ys den) (xs.length + ys.length + 1) := by
    convert KS.W28.FixedCompare.compare_spec_linear comparePorts copied using 1 <;>
      first | rfl | (funext j; fin_cases j <;> rfl)
  convert (hl.compose hr).compose hc using 1 <;> first | rfl | omega

def orderedBranch : Program 16 := KS.W29.FixedBranch.branch
  (compose (KS.W04.BinaryStackMoves.clearProgram 12) leftLargeProgram)
  (compose (KS.W04.BinaryStackMoves.clearProgram 12) rightLargeProgram)
  10 (KS.W06.RationalCompare.signSelect 12)

theorem orderedBranch_spec (sa sb : Bool) (xs ys den : List Bool) :
    RunSpec orderedBranch (comparedState sa xs sb ys den)
      (if KS.W19.bitsValue xs ≤ KS.W19.bitsValue ys then
        readyState sb (Computability.encodeNat (KS.W19.bitsValue ys - KS.W19.bitsValue xs)) den
      else readyState sa (Computability.encodeNat (KS.W19.bitsValue xs - KS.W19.bitsValue ys)) den)
      (arithmeticBudget xs ys den + 3) := by
  have hc : RunSpec (KS.W04.BinaryStackMoves.clearProgram 12)
      (comparedState sa xs sb ys den) (signedState sa xs sb ys den) 2 := by
    convert clear_spec (12 : Fin 16) (comparedState sa xs sb ys den) using 1 <;>
      first | rfl | (funext j; fin_cases j <;> rfl)
  by_cases ho : KS.W19.bitsValue xs ≤ KS.W19.bitsValue ys
  · simp only [ite_eq_left ho]
    have h := branch_spec_right
      (compose (KS.W04.BinaryStackMoves.clearProgram 12) leftLargeProgram)
      (compose (KS.W04.BinaryStackMoves.clearProgram 12) rightLargeProgram)
      (10 : Fin 16) (KS.W06.RationalCompare.signSelect 12)
      _ _ _ (by intro coin; simp [KS.W06.RationalCompare.signSelect, observedHeads,
        comparedState, KS.W29.topCode, ho]) (hc.compose (rightLarge_spec sa sb xs ys den ho))
    convert h using 1 <;> first | rfl | omega
  · simp only [ite_eq_right ho]
    have h := branch_spec_left
      (compose (KS.W04.BinaryStackMoves.clearProgram 12) leftLargeProgram)
      (compose (KS.W04.BinaryStackMoves.clearProgram 12) rightLargeProgram)
      (10 : Fin 16) (KS.W06.RationalCompare.signSelect 12)
      _ _ _ (by intro coin; simp [KS.W06.RationalCompare.signSelect, observedHeads,
        comparedState, KS.W29.topCode, ho]) (hc.compose (leftLarge_spec sa sb xs ys den (by omega)))
    convert h using 1 <;> first | rfl | omega

def differentProgram : Program 16 := compose copyCompareProgram orderedBranch

def equalSignSelect (heads : Fin 16 → Fin 3) (_coin : Bool) : KS.W29.FixedBranch.SelectInstruction 16 :=
  ⟨if heads 1 = heads 4 then .left else .right, KS.W06.RationalCompare.stayActions 16⟩

def signedProgram : Program 16 := KS.W29.FixedBranch.branch equalProgram differentProgram 10 equalSignSelect

def signedBudget (xs ys den : List Bool) : ℕ := 32 * (xs.length + ys.length + den.length + 1)

theorem signed_spec (sa sb : Bool) (xs ys den : List Bool) :
    RunSpec signedProgram (signedState sa xs sb ys den)
      (readyState (signedNumerator sa xs sb ys).1 (signedNumerator sa xs sb ys).2 den)
      (signedBudget xs ys den) := by
  by_cases he : sa = sb
  · subst sb
    have h := branch_spec_left equalProgram differentProgram (10 : Fin 16) equalSignSelect
      _ _ _ (by intro coin; simp [equalSignSelect, observedHeads, signedState])
      (equal_spec sa sa xs ys den)
    have h' : RunSpec signedProgram (signedState sa xs sa ys den)
        (readyState (signedNumerator sa xs sa ys).1 (signedNumerator sa xs sa ys).2 den)
        (arithmeticBudget xs ys den + 1) := by simpa [signedProgram, signedNumerator] using h
    apply h'.mono
    unfold signedBudget arithmeticBudget
    omega
  · have h := (copyCompare_spec sa sb xs ys den).compose (orderedBranch_spec sa sb xs ys den)
    have hb := branch_spec_right equalProgram differentProgram (10 : Fin 16) equalSignSelect
      _ _ _ (by intro coin; cases sa <;> cases sb <;>
        simp_all [equalSignSelect, observedHeads, signedState, KS.W29.topCode]) h
    have h' : RunSpec signedProgram (signedState sa xs sb ys den)
        (readyState (signedNumerator sa xs sb ys).1 (signedNumerator sa xs sb ys).2 den)
        ((3 * xs.length + 3 * ys.length + 5) + (arithmeticBudget xs ys den + 3) + 1) := by
      convert hb using 1 <;> (try rfl)
      unfold signedNumerator
      split_ifs <;> simp_all
    apply h'.mono
    unfold signedBudget arithmeticBudget
    omega

end KS.W13.RationalAdd

end OAI
