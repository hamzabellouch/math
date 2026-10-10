import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedLabelYY
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedLabelProgram

namespace OAI

/-! Literal fixed-size programs for the triple partition and YY/private
blocks. The branch tests inspect only the stored support labels. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelData
open ExactQuantumFactoring.BitStackProgram

noncomputable opaque entryProgram (k : ℕ) : Procedure labelsCode labelCode
    (fun xs => (xs.drop k).headD (0,0)) :=
  (Procedure.listGet labelCode (0,0)).comp
    ((Procedure.constant labelsCode Nat.bits k).pair (Procedure.identity labelsCode))
noncomputable opaque labelTest (k a : ℕ) : Procedure labelsCode Procedure.boolCode
    (fun xs => decide (((xs.drop k).headD (0,0)).2=a)) :=
  Procedure.binaryEq.comp (((Procedure.second Nat.bits Nat.bits).comp (entryProgram k)).pair
    (Procedure.constant labelsCode Nat.bits a))
noncomputable opaque lengthTest (n : ℕ) : Procedure labelsCode Procedure.boolCode
    (fun xs => decide (xs.length=n)) :=
  Procedure.binaryEq.comp ((Procedure.unaryToBits.comp
    (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength labelCode (0,0))).pair
    (Procedure.constant labelsCode Nat.bits n))

private def selected (a b : ℕ) (xs : List Letter) : List Letter :=
  [(xs.drop a).headD (0,0),(xs.drop b).headD (0,0)]
private noncomputable def selectedProgram (a b : ℕ) : Procedure labelsCode labelsCode
    (selected a b) :=
  (Procedure.listCons labelCode).comp ((entryProgram a).pair
    (singletonProgram _ (entryProgram b)))

private def partitionLookup (xs : List Letter) : List Letter × List Letter :=
  if xs.length=3 then
    if ((xs.drop 0).headD (0,0)).2=2 then
      if ((xs.drop 1).headD (0,0)).2=2 then
        (selected 0 1 xs,[(xs.drop 2).headD (0,0)])
      else (selected 0 2 xs,[(xs.drop 1).headD (0,0)])
    else (selected 1 2 xs,[(xs.drop 0).headD (0,0)])
  else (xs,[])

private theorem partitionLookup_eq (xs : List Letter) : partitionLookup xs=partition xs := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    cases xs with
    | nil => rfl
    | cons b xs =>
      cases xs with
      | nil => rfl
      | cons c xs =>
        cases xs with
        | nil => simp [partitionLookup,partition,selected]
        | cons d xs => simp [partitionLookup,partition,List.length_cons]

noncomputable opaque partitionProgram :
    Procedure labelsCode (prodCode labelsCode labelsCode) partition := by
  let p01 := (selectedProgram 0 1).pair (singletonProgram _ (entryProgram 2))
  let p02 := (selectedProgram 0 2).pair (singletonProgram _ (entryProgram 1))
  let p12 := (selectedProgram 1 2).pair (singletonProgram _ (entryProgram 0))
  let p := Procedure.conditional (lengthTest 3)
    (Procedure.conditional (labelTest 0 2) (Procedure.conditional (labelTest 1 2) p01 p02) p12)
    ((Procedure.identity labelsCode).pair (Procedure.constant labelsCode labelsCode []))
  exact p.congrFun (by
    intro xs
    simpa only [partitionLookup,decide_eq_true_eq,id_eq] using partitionLookup_eq xs)

noncomputable opaque pairLabelsProgram : Procedure blockCode labelsCode
    (fun x => (partition x.2).1) :=
  ((Procedure.first labelsCode labelsCode).comp partitionProgram).comp labelsProgram
noncomputable opaque realLabelsProgram : Procedure blockCode labelsCode
    (fun x => (partition x.2).2) :=
  ((Procedure.second labelsCode labelsCode).comp partitionProgram).comp labelsProgram
noncomputable opaque thirdMediatorProgram : Procedure blockCode labelCode
    (fun x => (x.1,axis ((partition x.2).1.take 1))) :=
  mediatorProgram.pair (axisProgram.comp ((takeProgram 1).comp pairLabelsProgram))

noncomputable opaque thirdBlockProgram (k : Fin 7) :
    Procedure blockCode labelsCode (fun x => thirdBlock x.1 x.2 k) := by
  refine Fin.cases ?_ (fun k => ?_) k
  · exact Procedure.constant blockCode labelsCode []
  · refine Fin.cases ?_ (fun k => ?_) k
    · exact singletonProgram (fun x : BlockInput => (x.1,3))
        (mediatorProgram.pair (Procedure.constant blockCode Nat.bits 3))
    · refine Fin.cases ?_ (fun k => ?_) k
      · exact pairLabelsProgram
      · refine Fin.cases ?_ (fun k => ?_) k
        · exact realLabelsProgram
        · refine Fin.cases ?_ (fun k => ?_) k
          · exact (Procedure.listAppend labelCode (0,0)).comp
              (realLabelsProgram.pair (singletonProgram (fun x : BlockInput => (x.1,3))
                (mediatorProgram.pair (Procedure.constant blockCode Nat.bits 3))))
          · refine Fin.cases ?_ (fun k => ?_) k
            · exact (Procedure.listAppend labelCode (0,0)).comp
                (((takeProgram 1).comp pairLabelsProgram).pair
                  (singletonProgram _ thirdMediatorProgram))
            · refine Fin.cases ?_ (fun k => Fin.elim0 k) k
              exact (Procedure.listAppend labelCode (0,0)).comp
                (((dropProgram 1).comp pairLabelsProgram).pair
                  (singletonProgram _ thirdMediatorProgram))

noncomputable opaque zerosProgram : Procedure labelsCode labelsCode zeros :=
  Procedure.listMap (0,0) (0,0) ((Procedure.first Nat.bits Nat.bits).pair
    (Procedure.constant labelCode Nat.bits 0))

private def yyLookup (xs : List Letter) : List Letter × List Letter :=
  if xs.length=2 ∧ ((xs.drop 0).headD (0,0)).2=2 then
    ([(((xs.drop 0).headD (0,0)).1,1),(((xs.drop 1).headD (0,0)).1,3)],
     [(((xs.drop 0).headD (0,0)).1,3),(((xs.drop 1).headD (0,0)).1,1)])
  else (xs,zeros xs)
private theorem yyLookup_eq (xs : List Letter) : yyLookup xs=yyFactors xs := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    cases xs with
    | nil => simp [yyLookup,yyFactors]
    | cons b xs =>
      cases xs with
      | nil => simp [yyLookup,yyFactors]
      | cons c xs => simp [yyLookup,yyFactors,List.length_cons]

private noncomputable def relabelProgram (k a : ℕ) : Procedure labelsCode labelCode
    (fun xs => (((xs.drop k).headD (0,0)).1,a)) :=
  ((Procedure.first Nat.bits Nat.bits).comp (entryProgram k)).pair
    (Procedure.constant labelsCode Nat.bits a)
private noncomputable def crossedProgram (a b : ℕ) : Procedure labelsCode labelsCode
    (fun xs => [(((xs.drop 0).headD (0,0)).1,a),(((xs.drop 1).headD (0,0)).1,b)]) :=
  (Procedure.listCons labelCode).comp ((relabelProgram 0 a).pair
    (singletonProgram _ (relabelProgram 1 b)))
noncomputable opaque yyFactorsProgram : Procedure labelsCode (prodCode labelsCode labelsCode)
    yyFactors := by
  let p := Procedure.conditional (Procedure.boolAnd.comp
      ((lengthTest 2).pair (labelTest 0 2)))
    ((crossedProgram 1 3).pair (crossedProgram 3 1))
    ((Procedure.identity labelsCode).pair zerosProgram)
  exact p.congrFun (by
    intro xs
    simpa only [yyLookup,Function.comp_apply,id_eq,Bool.and_eq_true,decide_eq_true_eq]
      using yyLookup_eq xs)

noncomputable opaque yyBlockProgram (k : Fin 4) :
    Procedure blockCode labelsCode (fun x => yyBlock x.1 x.2 k) := by
  let med := singletonProgram (fun x : BlockInput => (x.1,1))
    (mediatorProgram.pair (Procedure.constant blockCode Nat.bits 1))
  refine Fin.cases ?_ (fun k => ?_) k
  · exact Procedure.constant blockCode labelsCode []
  · refine Fin.cases ?_ (fun k => ?_) k
    · exact singletonProgram (fun x : BlockInput => (x.1,3))
        (mediatorProgram.pair (Procedure.constant blockCode Nat.bits 3))
    · refine Fin.cases ?_ (fun k => ?_) k
      · exact (Procedure.listAppend labelCode (0,0)).comp
          ((((Procedure.first labelsCode labelsCode).comp yyFactorsProgram).comp labelsProgram).pair med)
      · refine Fin.cases ?_ (fun k => Fin.elim0 k) k
        exact (Procedure.listAppend labelCode (0,0)).comp
          ((((Procedure.second labelsCode labelsCode).comp yyFactorsProgram).comp labelsProgram).pair med)

noncomputable opaque privateBlockProgram (k : Fin 4) :
    Procedure blockCode labelsCode (fun x => privateBlock x.1 x.2 k) := by
  let med := singletonProgram (fun x : BlockInput => (x.1,1))
    (mediatorProgram.pair (Procedure.constant blockCode Nat.bits 1))
  refine Fin.cases ?_ (fun k => ?_) k
  · exact Procedure.constant blockCode labelsCode []
  · refine Fin.cases ?_ (fun k => ?_) k
    · exact singletonProgram (fun x : BlockInput => (x.1,3))
        (mediatorProgram.pair (Procedure.constant blockCode Nat.bits 3))
    · refine Fin.cases ?_ (fun k => ?_) k
      · exact (Procedure.listAppend labelCode (0,0)).comp ((prefixProgram 1).pair med)
      · refine Fin.cases ?_ (fun k => Fin.elim0 k) k
        exact (Procedure.listAppend labelCode (0,0)).comp ((suffixProgram 1).pair med)

end ContinuumCoulomb.QuantumOrderedLabelData

end

end OAI
