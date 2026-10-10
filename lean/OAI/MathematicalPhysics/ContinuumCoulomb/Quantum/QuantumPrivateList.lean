import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPrivateProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPrivateFamily

namespace OAI

/-! Polynomial enumeration of the complete private subdivision and its scale. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPrivate
open QuantumRawExchange ExactQuantumFactoring.BitStackProgram

def rawBudget (xs : List Raw) : ℚ := 4*(1+(xs.map (fun x => (1+|x.2.2.2|)^2)).sum)
def rawScale (N : ℕ) (xs : List Raw) : ℚ := 8*(rawBudget xs)^4*N

def subdivide (x : ScheduleInput) : List Raw :=
  ((List.range x.2.2.length).map (fun e => rawBlock x.1 e (rawScale x.2.1 x.2.2)
    ((x.2.2.drop e).headD zeroRaw))).flatten

def output (x : ScheduleInput) : ScheduleInput := (x.1+x.2.2.length,x.2.1,subdivide x)
def compile (x : ScheduleInput) : List MediatorListProgram.Bond × ℚ := QuantumRawExchange.compile (output x)

noncomputable opaque rawWeightMagnitudeProgram : Procedure rawCode ratCode (fun x => 1+|x.2.2.2|) :=
  Procedure.ratAdd.comp ((Procedure.constant rawCode ratCode 1).pair rawAbsoluteProgram)
noncomputable opaque rawWeightSquareProgram : Procedure rawCode ratCode (fun x => (1+|x.2.2.2|)^2) :=
  (Procedure.ratMul.comp (rawWeightMagnitudeProgram.pair rawWeightMagnitudeProgram)).congrFun
    (by intro x; change _*_ = _^2; ring)
noncomputable opaque rawSumProgram : Procedure (listCode rawCode) ratCode
    (fun xs => (xs.map (fun x => (1+|x.2.2.2|)^2)).sum) :=
  RationalSumProgram.sumProgram.comp (Procedure.listMap zeroRaw 0 rawWeightSquareProgram)
noncomputable opaque budgetProgram : Procedure scheduleCode ratCode (fun x => rawBudget x.2.2) :=
  Procedure.ratMul.comp ((Procedure.constant scheduleCode ratCode 4).pair
    (Procedure.ratAdd.comp ((Procedure.constant scheduleCode ratCode 1).pair
      (rawSumProgram.comp scheduleTermsProgram))))
noncomputable opaque budgetSquareProgram : Procedure scheduleCode ratCode (fun x => (rawBudget x.2.2)^2) :=
  (Procedure.ratMul.comp (budgetProgram.pair budgetProgram)).congrFun
    (by intro x; change _*_ = _^2; ring)
noncomputable opaque budgetFourthProgram : Procedure scheduleCode ratCode (fun x => (rawBudget x.2.2)^4) :=
  (Procedure.ratMul.comp (budgetSquareProgram.pair budgetSquareProgram)).congrFun
    (by intro x; change _^2*_^2 = _^4; ring)
noncomputable opaque scaleProgram : Procedure scheduleCode ratCode (fun x => rawScale x.2.1 x.2.2) :=
  Procedure.ratMul.comp ((Procedure.ratMul.comp
    ((Procedure.constant scheduleCode ratCode 8).pair budgetFourthProgram)).pair accuracyRatProgram)
noncomputable opaque newCountProgram : Procedure scheduleCode unaryCode (fun x => x.1+x.2.2.length) :=
  Procedure.unaryAdd.comp (scheduleCountProgram.pair scheduleLengthProgram)
noncomputable opaque blockEnvironmentProgram : Procedure scheduleCode (prodCode Nat.bits ratCode)
    (fun x => (x.1,rawScale x.2.1 x.2.2)) :=
  (Procedure.unaryToBits.comp scheduleCountProgram).pair scaleProgram

def iterationCode : (ℕ × ScheduleInput) → List Bool := prodCode unaryCode scheduleCode
noncomputable opaque iterationIndexProgram : Procedure iterationCode Nat.bits Prod.fst :=
  Procedure.unaryToBits.comp (Procedure.first _ _)
noncomputable opaque iterationInputProgram : Procedure iterationCode scheduleCode Prod.snd := Procedure.second _ _
noncomputable opaque iterationRawProgram : Procedure iterationCode rawCode
    (fun x => ((x.2.2.2.drop x.1).headD zeroRaw)) :=
  (Procedure.listGet rawCode zeroRaw).comp
    (iterationIndexProgram.pair (scheduleTermsProgram.comp iterationInputProgram))
noncomputable opaque iterationBlockInputProgram : Procedure iterationCode blockCode
    (fun x => ((x.2.1,rawScale x.2.2.1 x.2.2.2),(x.1,(x.2.2.2.drop x.1).headD zeroRaw))) :=
  (blockEnvironmentProgram.comp iterationInputProgram).pair (iterationIndexProgram.pair iterationRawProgram)
noncomputable opaque iterationProgram : Procedure iterationCode (listCode rawCode)
    (fun x => rawBlock x.2.1 x.1 (rawScale x.2.2.1 x.2.2.2) ((x.2.2.2.drop x.1).headD zeroRaw)) :=
  (blockProgram.comp iterationBlockInputProgram).congrFun (by intro x; rfl)
noncomputable opaque tabulatedProgram : Procedure iterationCode (listCode (listCode rawCode))
    (fun x => (List.range x.1).map (fun e =>
      rawBlock x.2.1 e (rawScale x.2.2.1 x.2.2.2) ((x.2.2.2.drop e).headD zeroRaw))) :=
  Procedure.tabulate
    (ea := scheduleCode) (eb := listCode rawCode)
    (f := fun x e => rawBlock x.1 e (rawScale x.2.1 x.2.2) ((x.2.2.drop e).headD zeroRaw)) []
    iterationProgram
noncomputable opaque rowsInputProgram : Procedure scheduleCode iterationCode
    (fun x => (x.2.2.length,x)) := scheduleLengthProgram.pair (Procedure.identity scheduleCode)
noncomputable opaque rowsProgram : Procedure scheduleCode (listCode (listCode rawCode))
    (fun x => (List.range x.2.2.length).map (fun e =>
      rawBlock x.1 e (rawScale x.2.1 x.2.2) ((x.2.2.drop e).headD zeroRaw))) := by
  let p := tabulatedProgram.comp rowsInputProgram
  exact p.congrFun (by intro x; rfl)
noncomputable opaque subdivideProgram : Procedure scheduleCode (listCode rawCode) subdivide := by
  let p := (flattenProgram rawCode zeroRaw).comp rowsProgram
  exact p.congrFun (by intro x; rfl)
noncomputable opaque outputProgram : Procedure scheduleCode scheduleCode output :=
  newCountProgram.pair (accuracyProgram.pair subdivideProgram)
noncomputable opaque compileProgram : Procedure scheduleCode
    (prodCode (listCode MediatorListProgram.bondCode) ratCode) compile :=
  QuantumRawExchange.compileProgram.comp outputProgram
noncomputable def compileCertificate : Turing.TM2ComputableInPolyTime scheduleCode
    (prodCode (listCode MediatorListProgram.bondCode) ratCode) compile := compileProgram.toTM2

end ContinuumCoulomb.QuantumPrivate

end

end OAI
