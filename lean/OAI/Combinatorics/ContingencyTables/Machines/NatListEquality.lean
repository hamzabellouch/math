import OAI.Combinatorics.ContingencyTables.Machines.IntegerMatrixProgram

namespace OAI

/-! # Binary list equality for matching tabulated states and outputs -/

namespace ContingencyTables.NatListEquality
open MatchingFPRAS MatchingFPRAS.TreeTyped

def indices (z : List ℕ×List ℕ) : List ℕ := List.range z.1.length

def indicesRealizer : Realizer indices := composition (composition first listLength) range

lemma polynomial_indices : PolynomialTime indicesRealizer := by
  apply polynomial_boundedRange (polynomial_composition polynomial_first polynomial_listLength)
    Polynomial.X
  intro z
  simpa only [Polynomial.eval_X,Function.comp_apply] using
    (list_length_le_weight z.1).trans (weight_fst z)

def atEqual (z : (List ℕ×List ℕ)×ℕ) : Bool := decide (z.1.1.getD z.2 0=z.1.2.getD z.2 0)

def atEqualRealizer : Realizer atEqual :=
  composition (pair
    (composition (pair (composition first first) second) (getDFast 0))
    (composition (pair (composition first second) second) (getDFast 0))) natEqual

lemma polynomial_atEqual : PolynomialTime atEqualRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      (polynomial_getDFast 0))
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second) polynomial_second)
      (polynomial_getDFast 0))) polynomial_natEqual

def listEqual (z : List ℕ×List ℕ) : Bool :=
  decide (z.1.length=z.2.length) && (indices z).all (fun i => atEqual (z,i))

def listEqualRealizer : Realizer listEqual :=
  (composition (pair
    (composition (pair (composition first listLength) (composition second listLength)) natEqual)
    (composition (composition (pair identity indicesRealizer) (mapWith atEqualRealizer)) all))
    boolAnd).congr (by
      intro z
      simp only [Function.comp_apply,List.all_map,Function.comp_def,id_eq,listEqual])

theorem polynomial_listEqual : PolynomialTime listEqualRealizer := by
  unfold listEqualRealizer
  apply polynomial_congr
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_listLength)
      (polynomial_composition polynomial_second polynomial_listLength)) polynomial_natEqual)
    (polynomial_composition (polynomial_composition
      (polynomial_pair polynomial_identity polynomial_indices)
      (polynomial_mapWith polynomial_atEqual)) polynomial_all)) polynomial_boolAnd

theorem listEqual_true (xs ys : List ℕ) : listEqual (xs,ys)=true ↔ xs=ys := by
  simp only [listEqual,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true]
  constructor
  · rintro ⟨hlen,h⟩
    apply List.ext_getElem hlen
    intro i hi hj
    have hv:=of_decide_eq_true (h i (List.mem_range.mpr hi))
    simpa only [atEqual,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem hj,Option.getD_some] using hv
  · intro h
    subst ys
    exact ⟨rfl,fun _ _ => by simp [atEqual]⟩

end ContingencyTables.NatListEquality

end OAI
