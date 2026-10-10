import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawFamilyProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSampleBudget

namespace OAI

/-! All four-spin scales and precisions are computed from the raw finite input. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRawExchange
open QuantumAxisSample MediatorListProgram ExactQuantumFactoring.BitStackProgram

def mass (xs : List Raw) : ℚ := (xs.map (fun t => |t.2.2.2|)).sum
def size (xs : List Raw) : ℚ := xs.length+mass xs
def budget (xs : List Raw) : ℚ := 1+2000000*size xs+(7056*size xs)^2
def scale (N : ℕ) (xs : List Raw) : ℚ := 9*(budget xs)^3*N

abbrev ScheduleInput := ℕ × (ℕ × List Raw)
def scheduleCode : ScheduleInput → List Bool :=
  prodCode unaryCode (prodCode Nat.bits (listCode rawCode))

def errorBound (x : ScheduleInput) : ℚ :=
  universalErrorBudget x.1 x.2.2.length (scale x.2.1 x.2.2) (mass x.2.2)
def bits (x : ScheduleInput) : ℕ := QuantumAxisSample.precision (errorBound x) x.2.1
def scheduled (x : ScheduleInput) : FullInput := (x.1,(bits x,scale x.2.1 x.2.2),x.2.2)
def compile (x : ScheduleInput) : List Bond × ℚ := (fullBonds (scheduled x),fullScalar (scheduled x))

noncomputable opaque rawWeightProgram : Procedure rawCode ratCode (fun t => t.2.2.2) :=
  (Procedure.second _ _).comp ((Procedure.second _ _).comp (Procedure.second _ _))
noncomputable opaque rawAbsoluteProgram : Procedure rawCode ratCode (fun t => |t.2.2.2|) :=
  MediatorProgram.absoluteProgram.comp rawWeightProgram
noncomputable opaque massProgram : Procedure (listCode rawCode) ratCode mass :=
  RationalSumProgram.sumProgram.comp (Procedure.listMap zeroRaw 0 rawAbsoluteProgram)

noncomputable opaque scheduleCountProgram : Procedure scheduleCode unaryCode Prod.fst := Procedure.first _ _
noncomputable opaque scheduleTailProgram : Procedure scheduleCode
    (prodCode Nat.bits (listCode rawCode)) Prod.snd := Procedure.second _ _
noncomputable opaque accuracyProgram : Procedure scheduleCode Nat.bits (fun x => x.2.1) :=
  (Procedure.first _ _).comp scheduleTailProgram
noncomputable opaque scheduleTermsProgram : Procedure scheduleCode (listCode rawCode) (fun x => x.2.2) :=
  (Procedure.second _ _).comp scheduleTailProgram
noncomputable opaque scheduleLengthProgram : Procedure scheduleCode unaryCode (fun x => x.2.2.length) :=
  (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength rawCode zeroRaw).comp scheduleTermsProgram
noncomputable opaque scheduleLengthRatProgram : Procedure scheduleCode ratCode (fun x => (x.2.2.length:ℚ)) :=
  Procedure.natToRat.comp (Procedure.unaryToBits.comp scheduleLengthProgram)
noncomputable opaque scheduleMassProgram : Procedure scheduleCode ratCode (fun x => mass x.2.2) :=
  massProgram.comp scheduleTermsProgram
noncomputable opaque sizeProgram : Procedure scheduleCode ratCode (fun x => size x.2.2) :=
  Procedure.ratAdd.comp (scheduleLengthRatProgram.pair scheduleMassProgram)
noncomputable opaque linearBudgetProgram : Procedure scheduleCode ratCode (fun x => 2000000*size x.2.2) :=
  Procedure.ratMul.comp ((Procedure.constant scheduleCode ratCode 2000000).pair sizeProgram)
noncomputable opaque quadraticBaseProgram : Procedure scheduleCode ratCode (fun x => 7056*size x.2.2) :=
  Procedure.ratMul.comp ((Procedure.constant scheduleCode ratCode 7056).pair sizeProgram)
noncomputable opaque quadraticBudgetProgram : Procedure scheduleCode ratCode (fun x => (7056*size x.2.2)^2) :=
  (Procedure.ratMul.comp (quadraticBaseProgram.pair quadraticBaseProgram)).congrFun
    (by intro x; change _*_ = _^2; ring)
noncomputable opaque budgetProgram : Procedure scheduleCode ratCode (fun x => budget x.2.2) :=
  Procedure.ratAdd.comp ((Procedure.ratAdd.comp
    ((Procedure.constant scheduleCode ratCode 1).pair linearBudgetProgram)).pair quadraticBudgetProgram)
noncomputable opaque squareBudgetProgram : Procedure scheduleCode ratCode (fun x => (budget x.2.2)^2) :=
  (Procedure.ratMul.comp (budgetProgram.pair budgetProgram)).congrFun
    (by intro x; change _*_ = _^2; ring)
noncomputable opaque cubeBudgetProgram : Procedure scheduleCode ratCode (fun x => (budget x.2.2)^3) :=
  (Procedure.ratMul.comp (squareBudgetProgram.pair budgetProgram)).congrFun
    (by intro x; change _^2*_ = _^3; ring)
noncomputable opaque accuracyRatProgram : Procedure scheduleCode ratCode (fun x => (x.2.1:ℚ)) :=
  Procedure.natToRat.comp accuracyProgram
noncomputable opaque scheduleScaleProgram : Procedure scheduleCode ratCode (fun x => scale x.2.1 x.2.2) :=
  Procedure.ratMul.comp ((Procedure.ratMul.comp
    ((Procedure.constant scheduleCode ratCode 9).pair cubeBudgetProgram)).pair accuracyRatProgram)
noncomputable opaque absoluteScaleProgram : Procedure scheduleCode ratCode (fun x => |scale x.2.1 x.2.2|) :=
  MediatorProgram.absoluteProgram.comp scheduleScaleProgram
noncomputable opaque countRatProgram : Procedure scheduleCode ratCode (fun x => (x.1:ℚ)) :=
  Procedure.natToRat.comp (Procedure.unaryToBits.comp scheduleCountProgram)
noncomputable opaque sixCountProgram : Procedure scheduleCode ratCode (fun x => 6*(x.1:ℚ)) :=
  Procedure.ratMul.comp ((Procedure.constant scheduleCode ratCode 6).pair countRatProgram)
noncomputable opaque termCountProgram : Procedure scheduleCode ratCode (fun x => 25*(x.2.2.length:ℚ)) :=
  Procedure.ratMul.comp ((Procedure.constant scheduleCode ratCode 25).pair scheduleLengthRatProgram)
noncomputable opaque edgeCountProgram : Procedure scheduleCode ratCode
    (fun x => 6*(x.1:ℚ)+25*(x.2.2.length:ℚ)) :=
  Procedure.ratAdd.comp (sixCountProgram.pair termCountProgram)
noncomputable opaque crossBudgetProgram : Procedure scheduleCode ratCode
    (fun x => 1568*|scale x.2.1 x.2.2| *(1+size x.2.2)) :=
  Procedure.ratMul.comp ((Procedure.ratMul.comp
    ((Procedure.constant scheduleCode ratCode 1568).pair absoluteScaleProgram)).pair
    (Procedure.ratAdd.comp ((Procedure.constant scheduleCode ratCode 1).pair sizeProgram)))
noncomputable opaque fieldBudgetProgram : Procedure scheduleCode ratCode (fun x => 26064*size x.2.2) :=
  Procedure.ratMul.comp ((Procedure.constant scheduleCode ratCode 26064).pair sizeProgram)
noncomputable opaque matrixBudgetProgram : Procedure scheduleCode ratCode
    (fun x => 3*(6*(x.1:ℚ)+25*(x.2.2.length:ℚ))*
      (1568*|scale x.2.1 x.2.2| *(1+size x.2.2)+26064*size x.2.2)) :=
  Procedure.ratMul.comp ((Procedure.ratMul.comp
    ((Procedure.constant scheduleCode ratCode 3).pair edgeCountProgram)).pair
      (Procedure.ratAdd.comp (crossBudgetProgram.pair fieldBudgetProgram)))
noncomputable opaque scalarBudgetProgram : Procedure scheduleCode ratCode (fun x => 320800*mass x.2.2) :=
  Procedure.ratMul.comp ((Procedure.constant scheduleCode ratCode 320800).pair scheduleMassProgram)
noncomputable opaque errorBoundProgram : Procedure scheduleCode ratCode errorBound :=
  Procedure.ratAdd.comp (matrixBudgetProgram.pair scalarBudgetProgram)
noncomputable opaque bitsProgram : Procedure scheduleCode unaryCode bits :=
  QuantumAxisSample.precisionProgram.comp (errorBoundProgram.pair accuracyProgram)
noncomputable opaque scheduledProgram : Procedure scheduleCode fullCode scheduled :=
  scheduleCountProgram.pair ((bitsProgram.pair scheduleScaleProgram).pair scheduleTermsProgram)
noncomputable opaque compileProgram : Procedure scheduleCode (prodCode (listCode bondCode) ratCode) compile :=
  (fullBondsProgram.pair fullScalarProgram).comp scheduledProgram
noncomputable def compileCertificate : Turing.TM2ComputableInPolyTime scheduleCode
    (prodCode (listCode bondCode) ratCode) compile := compileProgram.toTM2

end ContinuumCoulomb.QuantumRawExchange

end

end OAI
