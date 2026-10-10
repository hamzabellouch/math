import OAI.Combinatorics.ContingencyTables.Transport.BoundedCellShift
import OAI.Combinatorics.ContingencyTables.Machines.NetworkFeasibilityProgram

namespace OAI

/-! # Binary subtraction at one list coordinate

The scan depends on the stored list length. The subtracted amount remains
binary throughout and never controls a loop.
-/

namespace ContingencyTables.ListSubtractProgram

open MatchingFPRAS.TreeTyped Polynomial

abbrev Input := (List ℕ×ℕ)×ℕ
abbrev Cell := Input×ℕ

def entry (z : Cell) : ℕ :=
  z.1.1.1.getD z.2 0-if z.2=z.1.1.2 then z.1.2 else 0

def entryRealizer : Realizer entry := by
  let read : Realizer (fun z : Cell=>z.1.1.1.getD z.2 0) :=
    composition (pair (composition (composition first first) first) second) (getDFast 0)
  let amount : Realizer (fun z : Cell=>if z.2=z.1.1.2 then z.1.2 else 0) :=
    (choose (composition (pair second (composition (composition first first) second)) natEqual)
      (composition first second) (constant 0)).congr (by
        intro z
        simp only [Function.comp_apply,decide_eq_true_eq])
  exact composition (pair read amount) subtract

lemma polynomial_entry : PolynomialTime entryRealizer := by
  unfold entryRealizer
  apply polynomial_composition
  · apply polynomial_pair
    · exact polynomial_composition (polynomial_pair
        (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
          polynomial_first) polynomial_second) (polynomial_getDFast 0)
    · exact polynomial_congr _ (polynomial_choose
        (polynomial_composition (polynomial_pair polynomial_second
          (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
            polynomial_second)) polynomial_natEqual)
        (polynomial_composition polynomial_first polynomial_second) (polynomial_constant 0))
  · exact polynomial_subtract

def indices (z : Input) : List ℕ := List.range z.1.1.length

def indicesRealizer : Realizer indices :=
  composition (composition (composition first first) listLength) range

lemma polynomial_indices : PolynomialTime indicesRealizer := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,eval_X] using
    (list_length_le_weight z.1.1).trans ((weight_fst z.1).trans (weight_fst z))

def subtractAt (z : Input) : List ℕ :=
  (indices z).map (fun i=>entry (z,i))

def subtractAtRealizer : Realizer subtractAt :=
  composition (pair identity indicesRealizer) (mapWith entryRealizer)

lemma polynomial_subtractAt : PolynomialTime subtractAtRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_indices)
    (polynomial_mapWith polynomial_entry)

lemma subtractAt_length (xs : List ℕ) (i t : ℕ) :
    (subtractAt ((xs,i),t)).length=xs.length := by
  simp [subtractAt,indices]

lemma subtractAt_ofFn {m : ℕ} (x : Fin m→ℕ) (i : Fin m) (t : ℕ) :
    subtractAt ((List.ofFn x,i.val),t)=List.ofFn (BoundedCellShift.margin x i t) := by
  simp only [subtractAt,indices,List.length_ofFn,DirectedBFSCode.range_eq_map,←List.ofFn_eq_map,
    List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  simp only [entry,List.getD_eq_getElem?_getD,List.getElem?_ofFn,BoundedCellShift.margin]
  by_cases h : j=i
  · subst j
    simp
  · have hn : j.val≠i.val := fun he=>h (Fin.ext he)
    simp [h,hn]

end ContingencyTables.ListSubtractProgram

end OAI
