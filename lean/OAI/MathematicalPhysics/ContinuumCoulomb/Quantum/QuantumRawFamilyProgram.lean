import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawTermProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.RationalSumProgram

namespace OAI

/-! The complete finite rational edge list and offset are computed in polynomial time. -/

noncomputable section
namespace ContinuumCoulomb.QuantumRawExchange
open QuantumAxisSample MediatorListProgram ExactQuantumFactoring.BitStackProgram

private theorem flatten_code_bound {α : Type} (ea : α → List Bool) (xs : List (List α)) :
    (listCode ea xs.flatten).length ≤ (listCode (listCode ea) xs).length := by
  induction xs with
  | nil => exact le_rfl
  | cons x xs ih =>
    have h := listCode_length_append ea x xs.flatten
    simp only [List.flatten_cons,listCode_length_cons]
    omega

private theorem fold_append {α : Type} (xs : List (List α)) (ys : List α) :
    xs.foldl (fun ys x => ys++x) ys = ys++xs.flatten := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons,ih,List.flatten_cons,List.append_assoc]

noncomputable def flattenProgram {α : Type} (ea : α → List Bool) (d : α) :
    Procedure (listCode (listCode ea)) (listCode ea) List.flatten := by
  let step := (Procedure.listAppend ea d).comp (Procedure.swap (listCode ea) (listCode ea))
  let p := Procedure.foldList [] step Polynomial.X (by
    intro xs ys i
    change (listCode ea ((xs.take i).foldl (fun ys x => ys++x) ys)).length ≤ _
    rw [fold_append]
    have h := listCode_length_append ea ys (xs.take i).flatten
    have hf := flatten_code_bound ea (xs.take i)
    have ht := listCode_length_take_le (listCode ea) i xs
    simp only [Polynomial.eval_X]
    omega)
  exact (p.comp ((Procedure.identity (listCode (listCode ea))).pair
    (Procedure.constant (listCode (listCode ea)) (listCode ea) []))).congrFun (by
      intro xs
      change xs.foldl (fun ys x => ys++x) [] = xs.flatten
      simpa only [List.nil_append] using fold_append xs [])

abbrev FamilyInput := Environment × List Raw
def familyCode : FamilyInput → List Bool := prodCode environmentCode (listCode rawCode)

def termBondsList (x : FamilyInput) : List Bond := (x.2.map (fun t => bonds (x.1,t))).flatten
def termScalarList (x : FamilyInput) : ℚ := (x.2.map (fun t => scalar (x.1,t))).sum

def zeroRaw : Raw := ((false,false),((0,0),((false,false),0)))

noncomputable opaque termBondsProgram : Procedure familyCode (listCode bondCode) termBondsList :=
  (flattenProgram bondCode zeroBond).comp
    (Procedure.listMapWith (ea := environmentCode) (eb := rawCode) (ec := listCode bondCode)
      (f := fun env t => bonds (env,t)) zeroRaw [] bondsProgram)

noncomputable opaque termScalarProgram : Procedure familyCode ratCode termScalarList :=
  RationalSumProgram.sumProgram.comp
    (Procedure.listMapWith (ea := environmentCode) (eb := rawCode) (ec := ratCode)
      (f := fun env t => scalar (env,t)) zeroRaw 0 scalarProgram)

abbrev PenaltyInput := ℕ × ℚ
def penaltyCode : PenaltyInput → List Bool := prodCode unaryCode ratCode

def penaltyBlock (r : ℚ) (i : ℕ) : List Bond :=
  List.ofFn fun e : Fin 6 => (4*i+(qmaFourEdgeLeft e).val,
    4*i+(qmaFourEdgeRight e).val,r^2)

def penalty (n : ℕ) (r : ℚ) : List Bond := ((List.range n).map (penaltyBlock r)).flatten

noncomputable opaque penaltyIndexProgram : Procedure penaltyCode Nat.bits Prod.fst :=
  Procedure.unaryToBits.comp (Procedure.first _ _)
noncomputable opaque penaltyScaleProgram : Procedure penaltyCode ratCode Prod.snd := Procedure.second _ _
noncomputable opaque penaltyBaseProgram : Procedure penaltyCode Nat.bits (fun x => 4*x.1) :=
  Procedure.binaryMul.comp ((Procedure.constant penaltyCode Nat.bits 4).pair penaltyIndexProgram)
noncomputable opaque penaltyShiftProgram (i : ℕ) : Procedure penaltyCode Nat.bits (fun x => 4*x.1+i) :=
  Procedure.binaryAdd.comp (penaltyBaseProgram.pair (Procedure.constant penaltyCode Nat.bits i))
noncomputable opaque penaltySquareProgram : Procedure penaltyCode ratCode (fun x => x.2^2) :=
  (Procedure.ratMul.comp (penaltyScaleProgram.pair penaltyScaleProgram)).congrFun
    (by intro x; change x.2*x.2 = x.2^2; ring)
noncomputable opaque penaltyBondProgram (e : Fin 6) : Procedure penaltyCode bondCode
    (fun x => (4*x.1+(qmaFourEdgeLeft e).val,4*x.1+(qmaFourEdgeRight e).val,x.2^2)) :=
  (penaltyShiftProgram _).pair ((penaltyShiftProgram _).pair penaltySquareProgram)
noncomputable opaque penaltyBlockProgram : Procedure penaltyCode (listCode bondCode)
    (fun x => penaltyBlock x.2 x.1) := fixedListProgram penaltyCode bondCode 6 _ penaltyBondProgram
noncomputable opaque penaltyProgram : Procedure penaltyCode (listCode bondCode)
    (fun x => penalty x.1 x.2) :=
  (flattenProgram bondCode zeroBond).comp (Procedure.tabulate [] penaltyBlockProgram)

abbrev FullInput := ℕ × FamilyInput
def fullCode : FullInput → List Bool := prodCode unaryCode familyCode

def fullBonds (x : FullInput) : List Bond := penalty x.1 x.2.1.2 ++ termBondsList x.2
def fullScalar (x : FullInput) : ℚ := x.2.1.2^2*(x.1*6)+termScalarList x.2

noncomputable opaque fullCountProgram : Procedure fullCode unaryCode Prod.fst := Procedure.first _ _
noncomputable opaque fullFamilyProgram : Procedure fullCode familyCode Prod.snd := Procedure.second _ _
noncomputable opaque fullScaleProgram : Procedure fullCode ratCode (fun x => x.2.1.2) :=
  (Procedure.second unaryCode ratCode).comp ((Procedure.first _ _).comp fullFamilyProgram)
noncomputable opaque fullPenaltyInputProgram : Procedure fullCode penaltyCode (fun x => (x.1,x.2.1.2)) :=
  fullCountProgram.pair fullScaleProgram
noncomputable opaque fullBondsProgram : Procedure fullCode (listCode bondCode) fullBonds :=
  (Procedure.listAppend bondCode zeroBond).comp ((penaltyProgram.comp fullPenaltyInputProgram).pair
    (termBondsProgram.comp fullFamilyProgram))
noncomputable opaque fullCountRatProgram : Procedure fullCode ratCode (fun x => (x.1:ℚ)) :=
  Procedure.natToRat.comp (Procedure.unaryToBits.comp fullCountProgram)
noncomputable opaque fullSixCountProgram : Procedure fullCode ratCode (fun x => (x.1:ℚ)*6) :=
  Procedure.ratMul.comp (fullCountRatProgram.pair (Procedure.constant fullCode ratCode 6))
noncomputable opaque fullPenaltyScalarProgram : Procedure fullCode ratCode (fun x => x.2.1.2^2*(x.1*6)) :=
  Procedure.ratMul.comp ((penaltySquareProgram.comp fullPenaltyInputProgram).pair fullSixCountProgram)
noncomputable opaque fullScalarProgram : Procedure fullCode ratCode fullScalar :=
  Procedure.ratAdd.comp (fullPenaltyScalarProgram.pair (termScalarProgram.comp fullFamilyProgram))

noncomputable def fullCertificate : Turing.TM2ComputableInPolyTime fullCode
    (prodCode (listCode bondCode) ratCode) (fun x => (fullBonds x,fullScalar x)) :=
  (fullBondsProgram.pair fullScalarProgram).toTM2

end ContinuumCoulomb.QuantumRawExchange

end

end OAI
