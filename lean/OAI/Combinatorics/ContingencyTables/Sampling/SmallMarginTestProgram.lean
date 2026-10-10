import OAI.Combinatorics.ContingencyTables.Sampling.SmallComplementProgram

namespace OAI

/-! # Polynomial residual-margin inequality and equality tests -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

abbrev MarginCheckData := ((List (ℕ×ℕ)×List ℕ)×(List ℕ×List ℕ))×ℕ

def marginList (row : Bool) (z : MarginCheckData) : List ℕ :=
  if row then z.1.2.1 else z.1.2.2

def marginListRealizer (row : Bool) : Realizer (marginList row) :=
  choose (constant row) (composition (composition first second) first)
    (composition (composition first second) second)

lemma polynomial_marginList (row : Bool) : PolynomialTime (marginListRealizer row) :=
  polynomial_choose (polynomial_constant row)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_first)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_second)

def lineArgument (row : Bool) (z : MarginCheckData×ℕ) : LineData :=
  ((z.1.1.1,marginList (!row) z.1),z.2)

def lineArgumentRealizer (row : Bool) : Realizer (lineArgument row) :=
  pair (pair (composition (composition first first) first)
    (composition first (marginListRealizer (!row)))) second

lemma polynomial_lineArgument (row : Bool) : PolynomialTime (lineArgumentRealizer row) :=
  polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    (polynomial_composition polynomial_first (polynomial_marginList (!row)))) polynomial_second

def marginValueRealizer (row : Bool) : Realizer (fun z : MarginCheckData×ℕ =>
    (marginList row z.1).getD z.2 0) :=
  composition (pair (composition first (marginListRealizer row)) second) (getDFast 0)

lemma polynomial_marginValue (row : Bool) : PolynomialTime (marginValueRealizer row) :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first (polynomial_marginList row)) polynomial_second)
    (polynomial_getDFast 0)

def lineValueRealizer (row : Bool) : Realizer (fun z : MarginCheckData×ℕ =>
    lineSum row (lineArgument row z)) :=
  composition (f := lineArgument row) (g := lineSum row)
    (lineArgumentRealizer row) (lineSumRealizer row)

lemma polynomial_lineValue (row : Bool) : PolynomialTime (lineValueRealizer row) :=
  polynomial_composition (polynomial_lineArgument row) (polynomial_lineSum row)

def validMarginAt (row : Bool) (z : MarginCheckData×ℕ) : Bool :=
  let a := (marginList row z.1).getD z.2 0
  let s := lineSum row (lineArgument row z)
  decide (s≤a ∧ (a<z.1.2 → s=a))

def validMarginAtRealizer (row : Bool) : Realizer (validMarginAt row) :=
  (composition (pair
    (composition (pair (lineValueRealizer row) (marginValueRealizer row)) leNat)
    (choose (composition (pair (marginValueRealizer row) (composition first second)) less)
      (composition (pair (lineValueRealizer row) (marginValueRealizer row)) natEqual)
      (constant true))) boolAnd).congr (by
        intro z
        apply Bool.eq_iff_iff.mpr
        simp only [Function.comp_apply,Bool.and_eq_true,decide_eq_true_eq,validMarginAt]
        by_cases h : (marginList row z.1).getD z.2 0<z.1.2 <;>
          simp only [List.getD_eq_getElem?_getD] at h <;> simp [h])

lemma polynomial_validMarginAt (row : Bool) : PolynomialTime (validMarginAtRealizer row) := by
  unfold validMarginAtRealizer
  exact polynomial_congr _ (polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_lineValue row)
      (polynomial_marginValue row)) polynomial_leNat)
    (polynomial_choose (polynomial_composition (polynomial_pair (polynomial_marginValue row)
      (polynomial_composition polynomial_first polynomial_second)) polynomial_less)
      (polynomial_composition (polynomial_pair (polynomial_lineValue row)
        (polynomial_marginValue row)) polynomial_natEqual) (polynomial_constant true))) polynomial_boolAnd)

def marginIndices (row : Bool) : Realizer (fun z : MarginCheckData =>
    List.range (marginList row z).length) :=
  composition (composition (marginListRealizer row) listLength) range

lemma polynomial_marginIndices (row : Bool) : PolynomialTime (marginIndices row) := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_marginList row) polynomial_listLength) X
  intro z
  have hw : weight (marginList row z)≤weight z := by
    rcases z with ⟨⟨lookupData,⟨r,c⟩⟩,U⟩
    cases row <;> simp only [marginList,Bool.false_eq_true,ite_false,ite_true,weight_prod] <;> omega
  simpa only [Function.comp_apply,eval_X] using (list_length_le_weight (marginList row z)).trans hw

def validMargins (row : Bool) (z : MarginCheckData) : Bool :=
  (List.range (marginList row z).length).all (fun i => validMarginAt row (z,i))

def validMarginsRealizer (row : Bool) : Realizer (validMargins row) :=
  (composition (composition (pair identity (marginIndices row))
    (mapWith (validMarginAtRealizer row))) all).congr (by
      intro z
      simp only [Function.comp_apply,List.all_map,Function.comp_def,id_eq,validMargins])

theorem polynomial_validMargins (row : Bool) : PolynomialTime (validMarginsRealizer row) := by
  unfold validMarginsRealizer
  exact polynomial_congr _ (polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_identity (polynomial_marginIndices row))
    (polynomial_mapWith (polynomial_validMarginAt row))) polynomial_all)

theorem validMargins_iff (row : Bool) (z : MarginCheckData) :
    validMargins row z=true ↔ ∀ i,i<(marginList row z).length →
      lineSum row (lineArgument row (z,i))≤(marginList row z).getD i 0 ∧
      ((marginList row z).getD i 0<z.2 →
        lineSum row (lineArgument row (z,i))=(marginList row z).getD i 0) := by
  simp only [validMargins,List.all_eq_true,List.mem_range,validMarginAt,decide_eq_true_eq]

end ContingencyTables.ProfilePrograms

end OAI
