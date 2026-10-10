import Mathlib
import OAI.Analysis.MatrixSigning.Machines.StackTransferSpecs
import OAI.Analysis.MatrixSigning.Arithmetic.RationalCompareProgram
import OAI.Analysis.MatrixSigning.Arithmetic.RationalMagnitudeMachine

namespace OAI

namespace KS.W15.RationalMultiply
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W06.RationalCompare (workFields product productProgram productTicks runSpec_liftPorts)

def numeratorPorts : Fin 7 ↪ Fin 13 := ⟨![9,2,5,7,10,11,12], by decide⟩
def denominatorPorts : Fin 7 ↪ Fin 13 := ⟨![9,3,6,8,10,11,12], by decide⟩

def productsProgram : Program 13 :=
  compose (KS.W29.FixedSequential.liftPorts productProgram numeratorPorts)
    (KS.W29.FixedSequential.liftPorts productProgram denominatorPorts)

def productsAfter (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    Fin 13 → List Bool :=
  ![[],[sa],[],[],[sb],KS.W03.MultiplicationLoop.advance na nb,
    KS.W03.MultiplicationLoop.advance da db,product na nb,product da db,[],[],[],[]]

theorem products_spec (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    RunSpec productsProgram (workFields [sa] na da [sb] nb db [] [])
      (productsAfter sa na da sb nb db) (productTicks na nb + productTicks da db) := by
  let middle : Fin 13 → List Bool :=
    ![[],[sa],[],da,[sb],KS.W03.MultiplicationLoop.advance na nb,db,product na nb,[],[],[],[],[]]
  have hn : RunSpec (KS.W29.FixedSequential.liftPorts productProgram numeratorPorts)
      (workFields [sa] na da [sb] nb db [] []) middle (productTicks na nb) := by
    have hl : RunSpec productProgram
        (fun i => workFields [sa] na da [sb] nb db [] [] (numeratorPorts i))
        (KS.W03.MultiplicationBody.registers [] [] (KS.W03.MultiplicationLoop.advance na nb)
          (product na nb) [] [] []) (productTicks na nb) := by
      convert KS.W06.RationalCompare.product_spec [] na nb using 1 <;>
        first | rfl | (funext j; fin_cases j <;> rfl)
    have h := runSpec_liftPorts productProgram numeratorPorts
      (workFields [sa] na da [sb] nb db [] []) _ _ hl
    convert h using 1
    first | rfl | (funext index; fin_cases index <;> rfl)
  have hd : RunSpec (KS.W29.FixedSequential.liftPorts productProgram denominatorPorts)
      middle (productsAfter sa na da sb nb db) (productTicks da db) := by
    have hl : RunSpec productProgram (fun i => middle (denominatorPorts i))
        (KS.W03.MultiplicationBody.registers [] [] (KS.W03.MultiplicationLoop.advance da db)
          (product da db) [] [] []) (productTicks da db) := by
      convert KS.W06.RationalCompare.product_spec [] da db using 1 <;>
        first | rfl | (funext j; fin_cases j <;> rfl)
    have h := runSpec_liftPorts productProgram denominatorPorts middle _ _ hl
    convert h using 1
    first | rfl | (funext index; fin_cases index <;> rfl)
  exact hn.compose hd

def xorDispatch (_ : Fin 1) (heads : Fin 13 → Fin 3) (_coin : Bool) : Instruction 13 1 :=
  ⟨none, Vector.ofFn (fun j => if j = 1 ∨ j = 4 then .pop
    else if j = 12 then .push (((heads 1).val == 2) ^^ ((heads 4).val == 2)) else .stay)⟩

def xorProgram : Program 13 := ofMachine (compile 0 1 12 xorDispatch)

def xorAfter (before : Fin 13 → List Bool) (sa sb : Bool) : Fin 13 → List Bool :=
  fun j => if j = 1 ∨ j = 4 then [] else if j = 12 then [sa ^^ sb] else before j

theorem xor_spec (before : Fin 13 → List Bool) (sa sb : Bool)
    (ha : before 1 = [sa]) (hb : before 4 = [sb]) (ho : before 12 = []) :
    RunSpec xorProgram before (xorAfter before sa sb) 1 := by
  unfold xorProgram
  apply KS.W03.MachineRoundTrip.runSpec_ofMachine
  intro bits hlen
  rcases bits with _ | ⟨coin, tail⟩
  · simp at hlen
  have ht : tail = [] := by apply List.length_eq_zero_iff.mp; simpa using hlen
  subst tail
  change (compile (0 : Fin 1) 1 12 xorDispatch).step
    (⟨some (0 : Fin 1), before⟩ : Config 13 1) coin = _
  erw [step_compile]
  apply congrArg (Config.mk none)
  funext j
  fin_cases j <;> cases sa <;> cases sb <;>
    simp [xorDispatch, xorAfter, Instruction.action, observedHeads, KS.W29.topCode,
      KS.W29.StackAction.apply, ha, hb, ho]

def cleanupProgram : Program 13 :=
  compose (compose (compose (compose (compose (compose
    (KS.W04.BinaryStackMoves.clearProgram 5) (KS.W04.BinaryStackMoves.clearProgram 6))
      xorProgram) (KS.W04.BinaryStackMoves.moveProgram 7 0))
        (KS.W04.BinaryStackMoves.moveProgram 0 10))
          (KS.W04.BinaryStackMoves.moveProgram 8 0))
            (KS.W04.BinaryStackMoves.moveProgram 0 11)

def cleanupTicks (na da nb db : List Bool) : Nat :=
  (KS.W03.MultiplicationLoop.advance na nb).length +
    (KS.W03.MultiplicationLoop.advance da db).length +
    2 * (product na nb).length + 2 * (product da db).length + 7

theorem cleanup_spec (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    RunSpec cleanupProgram (productsAfter sa na da sb nb db)
      (KS.W30.RationalMagnitudeMachine.state (product na nb) (product da db) (sa ^^ sb))
      (cleanupTicks na da nb db) := by
  let s0 := productsAfter sa na da sb nb db
  let s1 := clearAfter 5 s0
  let s2 := clearAfter 6 s1
  let s3 := xorAfter s2 sa sb
  let s4 := moveAfter 7 0 s3
  let s5 := moveAfter 0 10 s4
  let s6 := moveAfter 8 0 s5
  have h1 := clear_spec (5 : Fin 13) s0
  have h2 := clear_spec (6 : Fin 13) s1
  have h3 := xor_spec s2 sa sb rfl rfl rfl
  have h4 := move_spec (7 : Fin 13) 0 (by decide) s3
  have h5 := move_spec (0 : Fin 13) 10 (by decide) s4
  have h6 := move_spec (8 : Fin 13) 0 (by decide) s5
  have h7 := move_spec (0 : Fin 13) 11 (by decide) s6
  have h := (((((h1.compose h2).compose h3).compose h4).compose h5).compose h6).compose h7
  convert h using 1 <;> (try rfl)
  · funext j
    fin_cases j <;> simp [s0,s1,s2,s3,s4,s5,s6,productsAfter,clearAfter,moveAfter,xorAfter,
      KS.W30.RationalMagnitudeMachine.state,KS.W30.RationalMagnitudeMachine.«stacks»]
  · simp [s0,s1,s2,s3,s4,s5,s6,productsAfter,clearAfter,moveAfter,xorAfter,cleanupTicks]
    omega

end KS.W15.RationalMultiply

end OAI
