import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedLabelSubdivision
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedRawPackingProgram

namespace OAI

/-! Polynomial list programs for the literal support-label operations.
Only constant-length prefixes are split in the early gadget compiler. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelData
open ExactQuantumFactoring.BitStackProgram

abbrev labelCode := QuantumOrderedRawPacking.letterCode
abbrev labelsCode := listCode labelCode

noncomputable def takeProgram (d : ℕ) : Procedure labelsCode labelsCode
    (fun xs => xs.take d) := by
  induction d with
  | zero => exact (Procedure.constant labelsCode labelsCode []).congrFun (by intro xs; rfl)
  | succ d ih =>
    let cons := (Procedure.listCons labelCode).comp
      ((Procedure.listHead labelCode (0,0)).pair (ih.comp (Procedure.listTail labelCode)))
    exact (Procedure.conditional (Procedure.listEmpty labelCode)
      (Procedure.constant labelsCode labelsCode []) cons).congrFun (by
        intro xs
        cases xs <;> rfl)

noncomputable def dropProgram (d : ℕ) : Procedure labelsCode labelsCode
    (fun xs => xs.drop d) :=
  (Procedure.listDrop labelCode).comp
    ((Procedure.constant labelsCode Nat.bits d).pair (Procedure.identity labelsCode))

def oddLetters (xs : List Letter) : Bool :=
  xs.foldr (fun a b => xor (decide (a.2=2)) b) false

private theorem oddLetters_eq (xs : List Letter) :
    oddLetters xs=decide (Odd (yCount xs)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change xor (decide (a.2=2)) (oddLetters xs)=_
    rw [ih]
    by_cases ha : a.2=2
    · have hc : yCount (a::xs)=yCount xs+1 := by simp [yCount,ha]
      simp only [hc,Nat.odd_add_one,ha,decide_true,Bool.true_xor,decide_not]
    · have hc : yCount (a::xs)=yCount xs := by simp [yCount,ha]
      rw [hc]
      simp [ha]

private theorem fold_oddLetters (xs : List Letter) (b : Bool) :
    xs.foldl (fun b a => xor (decide (a.2=2)) b) b=xor (oddLetters xs) b := by
  induction xs generalizing b with
  | nil => simp [oddLetters]
  | cons a xs ih =>
    rw [List.foldl_cons,ih]
    change xor (oddLetters xs) (xor (decide (a.2=2)) b)=
      xor (xor (decide (a.2=2)) (oddLetters xs)) b
    cases b <;> cases ha : decide (a.2=2) <;> cases hx : oddLetters xs <;> rfl

noncomputable opaque oddProgram : Procedure labelsCode Procedure.boolCode
    (fun xs => decide (Odd (yCount xs))) := by
  let head := Procedure.first labelCode Procedure.boolCode
  let letter := (Procedure.second Nat.bits Nat.bits).comp head
  let test := Procedure.binaryEq.comp
    (letter.pair (Procedure.constant (prodCode labelCode Procedure.boolCode) Nat.bits 2))
  let state := Procedure.second labelCode Procedure.boolCode
  let step := Procedure.boolXor.comp (test.pair state)
  let fold := Procedure.foldList (0,0) step (Polynomial.C 1) (by
    intro xs b i
    simp only [Procedure.boolCode,List.length_singleton,Polynomial.eval_C]
    exact le_rfl)
  exact (fold.comp ((Procedure.identity labelsCode).pair
    (Procedure.constant labelsCode Procedure.boolCode false))).congrFun (by
      intro xs
      simp only [Function.comp_apply,id_eq,fold_oddLetters,Bool.xor_false,oddLetters_eq])

noncomputable opaque axisProgram : Procedure labelsCode Nat.bits axis :=
  (Procedure.conditional oddProgram (Procedure.constant labelsCode Nat.bits 2)
    (Procedure.constant labelsCode Nat.bits 1)).congrFun (by
      intro xs
      simp only [axis,decide_eq_true_eq])

abbrev BlockInput := ℕ × List Letter
abbrev blockCode := prodCode Nat.bits labelsCode
noncomputable opaque mediatorProgram : Procedure blockCode Nat.bits Prod.fst := Procedure.first _ _
noncomputable opaque labelsProgram : Procedure blockCode labelsCode Prod.snd := Procedure.second _ _
noncomputable opaque prefixProgram (d : ℕ) : Procedure blockCode labelsCode
    (fun x => x.2.take d) := (takeProgram d).comp labelsProgram
noncomputable opaque suffixProgram (d : ℕ) : Procedure blockCode labelsCode
    (fun x => x.2.drop d) := (dropProgram d).comp labelsProgram
noncomputable opaque mediatorLabelProgram (d : ℕ) : Procedure blockCode labelCode
    (fun x => (x.1,axis (x.2.take d))) :=
  mediatorProgram.pair (axisProgram.comp (prefixProgram d))
noncomputable def singletonProgram {α : Type} {ea : α → List Bool}
    (f : α → Letter) (p : Procedure ea labelCode f) :
    Procedure ea labelsCode (fun x => [f x]) :=
  (Procedure.listCons labelCode).comp (p.pair (Procedure.constant ea labelsCode []))

noncomputable opaque subdivisionProgram (d : ℕ) (k : Fin 4) :
    Procedure blockCode labelsCode (fun x => subdivision x.1 d x.2 k) := by
  refine Fin.cases ?_ (fun k => ?_) k
  · exact Procedure.constant blockCode labelsCode []
  · refine Fin.cases ?_ (fun k => ?_) k
    · exact singletonProgram (fun x : BlockInput => (x.1,3))
        (mediatorProgram.pair (Procedure.constant blockCode Nat.bits 3))
    · refine Fin.cases ?_ (fun k => ?_) k
      · exact (Procedure.listAppend labelCode (0,0)).comp
          ((prefixProgram d).pair (singletonProgram _ (mediatorLabelProgram d)))
      · refine Fin.cases ?_ (fun k => Fin.elim0 k) k
        exact (Procedure.listAppend labelCode (0,0)).comp
          ((suffixProgram d).pair (singletonProgram _ (mediatorLabelProgram d)))

end ContinuumCoulomb.QuantumOrderedLabelData

end

end OAI
