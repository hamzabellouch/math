import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.RationalMultiplyProducts

namespace OAI

namespace KS.W13.RationalAdd

open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators
open KS.W06.RationalCompare (product productProgram productTicks)
open KS.W15.RationalMultiply (clear_spec clearAfter)

def corePorts : Fin 13 ↪ Fin 16 :=
  ⟨fun i => ⟨i.val, by omega⟩, by intro i j h; exact Fin.ext (congrArg (fun k : Fin 16 => k.val) h)⟩

def extend (s : Fin 13 → List Bool) (a b c : List Bool) : Fin 16 → List Bool := fun j =>
  if h : j.val < 13 then s ⟨j.val, h⟩ else if j = 13 then a else if j = 14 then b else c

@[simp] theorem extend_core (s : Fin 13 → List Bool) (a b c : List Bool) (i : Fin 13) :
    extend s a b c (corePorts i) = s i := by
  change dite (i.val < 13) (fun h => s ⟨i.val,h⟩) _ = s i
  exact dite_eq_left i.isLt

@[simp] theorem extend_13 (s : Fin 13 → List Bool) (a b c : List Bool) : extend s a b c 13 = a := rfl
@[simp] theorem extend_14 (s : Fin 13 → List Bool) (a b c : List Bool) : extend s a b c 14 = b := rfl
@[simp] theorem extend_15 (s : Fin 13 → List Bool) (a b c : List Bool) : extend s a b c 15 = c := rfl

theorem core_spec (P : Program 13) (before after : Fin 13 → List Bool)
    (a b c : List Bool) (ticks : ℕ) (h : RunSpec P before after ticks) :
    RunSpec (KS.W29.FixedSequential.liftPorts P corePorts)
      (extend before a b c) (extend after a b c) ticks := by
  apply KS.W01.FixedPortRunSpec.lift_runSpec P corePorts before after _ _ ticks h
  · intro i; exact extend_core before a b c i
  · intro i; exact extend_core after a b c i
  · intro j hj
    by_cases hsmall : j.val < 13
    · exact (hj ⟨j.val, hsmall⟩ (Fin.ext rfl)).elim
    · simp [extend, hsmall]

def prepareProgram : Program 16 :=
  KS.W29.FixedSequential.liftPorts KS.W06.RationalCompare.prepareProgram corePorts

def inputState (input : List Bool) : Fin 16 → List Bool :=
  extend (KS.W06.RationalCompare.fields input [] [] [] [] [] []) [] [] []

def preparedState (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) : Fin 16 → List Bool :=
  extend (KS.W06.RationalCompare.workFields [sa] na da [sb] nb db [] []) [] [] []

theorem prepare_spec (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    RunSpec prepareProgram (inputState (KS.W06.RationalCompare.pairBits sa na da sb nb db))
      (preparedState sa (KS.W06.RationalCompare.magnitude sa na) da
        sb (KS.W06.RationalCompare.magnitude sb nb) db)
      (KS.W06.RationalCompare.parseTicks na da nb db + (2 * na.length + 4) + (2 * nb.length + 4)) :=
  core_spec _ _ _ [] [] [] _ (KS.W06.RationalCompare.prepare_spec sa na da sb nb db)

def leftDenCopyPorts : Fin 3 ↪ Fin 16 := ⟨![3,13,9], by decide⟩
def rightDenCopyPorts : Fin 3 ↪ Fin 16 := ⟨![6,14,9], by decide⟩
def denominatorProductPorts : Fin 7 ↪ Fin 16 := ⟨![9,13,14,15,10,11,12], by decide⟩

def saveDenominators : Program 16 :=
  compose (KS.W01.FixedCopy.program leftDenCopyPorts) (KS.W01.FixedCopy.program rightDenCopyPorts)

def savedState (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) : Fin 16 → List Bool :=
  extend (KS.W06.RationalCompare.workFields [sa] na da [sb] nb db [] []) da db []

theorem saveDenominators_spec (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    RunSpec saveDenominators (preparedState sa na da sb nb db) (savedState sa na da sb nb db)
      ((2 * da.length + 2) + (2 * db.length + 2)) := by
  let middle := extend (KS.W06.RationalCompare.workFields [sa] na da [sb] nb db [] []) da [] []
  have hl : RunSpec (KS.W01.FixedCopy.program leftDenCopyPorts)
      (preparedState sa na da sb nb db) middle (2 * da.length + 2) := by
    apply KS.W03.MachineRoundTrip.runSpec_ofMachine (KS.W01.FixedCopy.machine leftDenCopyPorts)
    intro bits hb
    have h := KS.W01.FixedCopy.run_copy_restore leftDenCopyPorts (preparedState sa na da sb nb db)
      da bits rfl rfl rfl hb
    refine h.trans ?_
    apply congrArg (Config.mk none)
    funext j
    fin_cases j <;> rfl
  have hr : RunSpec (KS.W01.FixedCopy.program rightDenCopyPorts)
      middle (savedState sa na da sb nb db) (2 * db.length + 2) := by
    apply KS.W03.MachineRoundTrip.runSpec_ofMachine (KS.W01.FixedCopy.machine rightDenCopyPorts)
    intro bits hb
    have h := KS.W01.FixedCopy.run_copy_restore rightDenCopyPorts middle db bits rfl rfl rfl hb
    refine h.trans ?_
    apply congrArg (Config.mk none)
    funext j
    fin_cases j <;> rfl
  exact hl.compose hr

def crossProductsProgram : Program 16 :=
  KS.W29.FixedSequential.liftPorts KS.W06.RationalCompare.productsProgram corePorts

def denominatorProductProgram : Program 16 :=
  KS.W29.FixedSequential.liftPorts productProgram denominatorProductPorts

def productsAfter (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) : Fin 16 → List Bool :=
  extend (KS.W06.RationalCompare.productsAfter sa na da sb nb db) []
    (KS.W03.MultiplicationLoop.advance da db) (product da db)

theorem denominatorProduct_spec (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    RunSpec denominatorProductProgram
      (extend (KS.W06.RationalCompare.productsAfter sa na da sb nb db) da db [])
      (productsAfter sa na da sb nb db) (productTicks da db) := by
  let before := extend (KS.W06.RationalCompare.productsAfter sa na da sb nb db) da db []
  have hlocal : RunSpec productProgram (fun i => before (denominatorProductPorts i))
      (KS.W03.MultiplicationBody.registers [] [] (KS.W03.MultiplicationLoop.advance da db)
        (product da db) [] [] []) (productTicks da db) := by
    convert KS.W06.RationalCompare.product_spec [] da db using 1 <;>
      first | rfl | (funext i; fin_cases i <;> rfl)
  have h := KS.W06.RationalCompare.runSpec_liftPorts productProgram denominatorProductPorts before _ _ hlocal
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;> rfl)

def productsProgram : Program 16 :=
  compose (compose saveDenominators crossProductsProgram) denominatorProductProgram

def productsTicks (na da nb db : List Bool) : ℕ :=
  ((2 * da.length + 2) + (2 * db.length + 2)) +
    (productTicks na db + productTicks nb da) + productTicks da db

theorem products_spec (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    RunSpec productsProgram (preparedState sa na da sb nb db) (productsAfter sa na da sb nb db)
      (productsTicks na da nb db) := by
  have hcross := core_spec KS.W06.RationalCompare.productsProgram _ _ da db [] _
    (KS.W06.RationalCompare.products_spec sa na da sb nb db)
  exact ((saveDenominators_spec sa na da sb nb db).compose hcross).compose
    (denominatorProduct_spec sa na da sb nb db)

def signedState (sa : Bool) (xs : List Bool) (sb : Bool) (ys den : List Bool) : Fin 16 → List Bool :=
  ![[],[sa],[],[],[sb],[],[],xs,ys,[],[],[],[],[],[],den]

def clearProductsProgram : Program 16 :=
  compose (compose (KS.W04.BinaryStackMoves.clearProgram 3) (KS.W04.BinaryStackMoves.clearProgram 6))
    (KS.W04.BinaryStackMoves.clearProgram 14)

def clearProductsTicks (na da nb db : List Bool) : ℕ :=
  (KS.W03.MultiplicationLoop.advance nb da).length + 1 +
    ((KS.W03.MultiplicationLoop.advance na db).length + 1) +
    ((KS.W03.MultiplicationLoop.advance da db).length + 1)

theorem clearProducts_spec (sa : Bool) (na da : List Bool) (sb : Bool) (nb db : List Bool) :
    RunSpec clearProductsProgram (productsAfter sa na da sb nb db)
      (signedState sa (product na db) sb (product nb da) (product da db))
      (clearProductsTicks na da nb db) := by
  have h1 := clear_spec (3 : Fin 16) (productsAfter sa na da sb nb db)
  have h2 := clear_spec (6 : Fin 16) (clearAfter 3 (productsAfter sa na da sb nb db))
  have h3 := clear_spec (14 : Fin 16) (clearAfter 6 (clearAfter 3 (productsAfter sa na da sb nb db)))
  have h := (h1.compose h2).compose h3
  convert h using 1 <;> first | rfl | (funext j; fin_cases j <;> rfl)

end KS.W13.RationalAdd

end OAI
