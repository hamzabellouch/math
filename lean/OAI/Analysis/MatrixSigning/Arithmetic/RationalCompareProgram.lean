import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.RationalCompareBranch
import OAI.Analysis.MatrixSigning.Arithmetic.RationalCompareParser

namespace OAI

section

namespace KS.W06.RationalCompare
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

def leftMagnitudePorts : Fin 3 ↪ Fin 13 := ⟨![10,2,11], by decide⟩
def rightMagnitudePorts : Fin 3 ↪ Fin 13 := ⟨![10,5,11], by decide⟩
def leftProductPorts : Fin 7 ↪ Fin 13 := ⟨![9,2,6,7,10,11,12], by decide⟩
def rightProductPorts : Fin 7 ↪ Fin 13 := ⟨![9,5,3,8,10,11,12], by decide⟩
def resultPorts : Fin 3 ↪ Fin 13 := ⟨![7,8,9], by decide⟩

def workFields (sa na da sb nb db left right : List Bool) : Fin 13 → List Bool :=
  ![[],sa,na,da,sb,nb,db,left,right,[],[],[],[]]

def magnitude (s : Bool) (xs : List Bool) : List Bool := KS.W01.MagnitudeProgram.result s xs
def product (xs ys : List Bool) : List Bool :=
  Computability.encodeNat (KS.W19.bitsValue xs * KS.W19.bitsValue ys)

def prepareProgram : Program 13 :=
  compose (compose parseProgram (magnitudeProgram leftMagnitudePorts 1))
    (magnitudeProgram rightMagnitudePorts 4)

theorem prepare_spec (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    RunSpec prepareProgram (fields (pairBits sa na da sb nb db) [] [] [] [] [] [])
      (workFields [sa] (magnitude sa na) da [sb] (magnitude sb nb) db [] [])
      (parseTicks na da nb db + (2 * na.length + 4) + (2 * nb.length + 4)) := by
  have hleft : RunSpec (magnitudeProgram leftMagnitudePorts 1)
      (fields [] [sa] na da [sb] nb db)
      (fields [] [sa] (magnitude sa na) da [sb] nb db) (2 * na.length + 4) := by
    have h := magnitude_spec leftMagnitudePorts 1 (fields [] [sa] na da [sb] nb db)
      sa na rfl rfl rfl rfl
    convert h using 1
    first | rfl | (funext index; fin_cases index <;> rfl)
  have hright : RunSpec (magnitudeProgram rightMagnitudePorts 4)
      (fields [] [sa] (magnitude sa na) da [sb] nb db)
      (workFields [sa] (magnitude sa na) da [sb] (magnitude sb nb) db [] [])
      (2 * nb.length + 4) := by
    have h := magnitude_spec rightMagnitudePorts 4
      (fields [] [sa] (magnitude sa na) da [sb] nb db) sb nb rfl rfl rfl rfl
    convert h using 1
    first | rfl | (funext index; fin_cases index <;> rfl)
  exact ((parse_spec sa na da sb nb db).compose hleft).compose hright

def productsProgram : Program 13 :=
  compose (KS.W29.FixedSequential.liftPorts productProgram leftProductPorts)
    (KS.W29.FixedSequential.liftPorts productProgram rightProductPorts)

def productsAfter (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) : Fin 13 → List Bool :=
  workFields [sa] [] (KS.W03.MultiplicationLoop.advance nb da) [sb] []
    (KS.W03.MultiplicationLoop.advance na db) (product na db) (product nb da)

theorem products_spec (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    RunSpec productsProgram (workFields [sa] na da [sb] nb db [] [])
      (productsAfter sa na da sb nb db) (productTicks na db + productTicks nb da) := by
  let middle := workFields [sa] [] da [sb] nb
    (KS.W03.MultiplicationLoop.advance na db) (product na db) []
  have hleft : RunSpec (KS.W29.FixedSequential.liftPorts productProgram leftProductPorts)
      (workFields [sa] na da [sb] nb db [] []) middle (productTicks na db) := by
    have hlocal : RunSpec productProgram
        (fun i => workFields [sa] na da [sb] nb db [] [] (leftProductPorts i))
        (KS.W03.MultiplicationBody.registers [] [] (KS.W03.MultiplicationLoop.advance na db)
          (product na db) [] [] []) (productTicks na db) := by
      convert product_spec [] na db using 1 <;> first | rfl | (funext j; fin_cases j <;> rfl)
    have h := runSpec_liftPorts productProgram leftProductPorts
      (workFields [sa] na da [sb] nb db [] []) _ _ hlocal
    convert h using 1
    first | rfl | (funext index; fin_cases index <;> rfl)
  have hright : RunSpec (KS.W29.FixedSequential.liftPorts productProgram rightProductPorts)
      middle (productsAfter sa na da sb nb db) (productTicks nb da) := by
    have hlocal : RunSpec productProgram (fun i => middle (rightProductPorts i))
        (KS.W03.MultiplicationBody.registers [] [] (KS.W03.MultiplicationLoop.advance nb da)
          (product nb da) [] [] []) (productTicks nb da) := by
      convert product_spec [] nb da using 1 <;> first | rfl | (funext j; fin_cases j <;> rfl)
    have h := runSpec_liftPorts productProgram rightProductPorts middle _ _ hlocal
    convert h using 1
    first | rfl | (funext index; fin_cases index <;> rfl)
  exact hleft.compose hright

def program : Program 13 :=
  compose (compose prepareProgram productsProgram) (signedCompareProgram resultPorts 1 4)

def machine : Machine := program.toMachine

def totalTicks (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) : ℕ :=
  let a := magnitude sa na
  let b := magnitude sb nb
  ((parseTicks na da nb db + (2 * na.length + 4) + (2 * nb.length + 4)) +
    (productTicks a db + productTicks b da)) +
    ((product a db).length + (product b da).length + 2)

def finalStacks (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) : Fin 13 → List Bool :=
  signedCompareAfter resultPorts
    (productsAfter sa (magnitude sa na) da sb (magnitude sb nb) db) sa sb

theorem full_spec (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    RunSpec program (fields (pairBits sa na da sb nb db) [] [] [] [] [] [])
      (finalStacks sa na da sb nb db) (totalTicks sa na da sb nb db) := by
  have hparse := prepare_spec sa na da sb nb db
  have hprod := products_spec sa (magnitude sa na) da sb (magnitude sb nb) db
  have hcompare := signedCompare_spec resultPorts 1 4
    (productsAfter sa (magnitude sa na) da sb (magnitude sb nb) db) sa sb rfl rfl
  exact (hparse.compose hprod).compose hcompare

theorem final_output (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    finalStacks sa na da sb nb db 9 =
      [signedCrossLE sa sb
        (KS.W19.bitsValue (magnitude sa na) * KS.W19.bitsValue db)
        (KS.W19.bitsValue (magnitude sb nb) * KS.W19.bitsValue da)] := by
  have h := signedCompareAfter_output resultPorts
    (productsAfter sa (magnitude sa na) da sb (magnitude sb nb) db) sa sb
  simpa [finalStacks, productsAfter, workFields, resultPorts, product,
    KS.W19.bitsValue_encodeNat] using h

@[simp] theorem machine_stackCount : machine.stackCount = 13 := rfl
@[simp] theorem machine_inputStack : machine.inputStack = (0 : Fin 13) := rfl
@[simp] theorem machine_outputStack : machine.outputStack = (9 : Fin 13) := rfl

theorem init_eq (input : List Bool) :
    machine.init input = ⟨some program.initial, fields input [] [] [] [] [] []⟩ := by
  apply congrArg (Config.mk (some program.initial))
  funext j
  fin_cases j <;> rfl

theorem run_input (sa : Bool) (na da : List Bool) (sb : Bool) (nb db bits : List Bool)
    (hlen : totalTicks sa na da sb nb db ≤ bits.length) :
    machine.run (machine.init (pairBits sa na da sb nb db)) bits =
      ⟨none, finalStacks sa na da sb nb db⟩ := by
  rw [init_eq]
  exact (full_spec sa na da sb nb db).run_of_le bits hlen

end KS.W06.RationalCompare

end

end OAI
