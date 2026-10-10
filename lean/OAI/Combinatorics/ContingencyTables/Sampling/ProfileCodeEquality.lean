import OAI.Combinatorics.ContingencyTables.Sampling.SmallProfileFlatCode
import OAI.Combinatorics.MatchingCount.Machines.TreeCanonical

namespace OAI

/-! # Polynomial equality and duplicate removal for profile codes -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

def listEntryEqual (z : (List ℕ×List ℕ)×ℕ) : Bool :=
  decide (z.1.1.getD z.2 0=z.1.2.getD z.2 0)

def listEntryEqualRealizer : Realizer listEntryEqual :=
  composition (pair
    (composition (pair (composition first first) second) (getDFast 0))
    (composition (pair (composition first second) second) (getDFast 0))) natEqual

lemma polynomial_listEntryEqual : PolynomialTime listEntryEqualRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      (polynomial_getDFast 0))
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second) polynomial_second)
      (polynomial_getDFast 0))) polynomial_natEqual

def equalityIndices : Realizer (fun z : List ℕ×List ℕ => List.range z.1.length) :=
  composition first profileIndices

lemma polynomial_equalityIndices : PolynomialTime equalityIndices :=
  polynomial_composition polynomial_first polynomial_profileIndices

def listNatTest (z : List ℕ×List ℕ) : Bool :=
  decide (z.1.length=z.2.length) &&
    (List.range z.1.length).all (fun i => listEntryEqual (z,i))

def listNatTestRealizer : Realizer listNatTest :=
  (composition (pair
    (composition (pair (composition first listLength) (composition second listLength)) natEqual)
    (composition (composition (pair identity equalityIndices) (mapWith listEntryEqualRealizer)) all))
      boolAnd).congr (by
        intro z
        simp only [Function.comp_apply,List.all_map,Function.comp_def,id_eq,listNatTest])

lemma polynomial_listNatTest : PolynomialTime listNatTestRealizer :=
  polynomial_congr _ (polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_listLength)
      (polynomial_composition polynomial_second polynomial_listLength)) polynomial_natEqual)
    (polynomial_composition (polynomial_composition
      (polynomial_pair polynomial_identity polynomial_equalityIndices)
      (polynomial_mapWith polynomial_listEntryEqual)) polynomial_all)) polynomial_boolAnd)

lemma listNatTest_iff (z : List ℕ×List ℕ) : listNatTest z=true ↔ z.1=z.2 := by
  rcases z with ⟨xs,ys⟩
  simp only [listNatTest,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.mem_range,
    listEntryEqual]
  constructor
  · rintro ⟨hlen,h⟩
    apply List.ext_getElem hlen
    intro i hi hj
    have he := h i hi
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem hj,Option.getD_some,decide_eq_true_eq] using he
  · rintro rfl
    simp

def listNatEqual : Realizer (fun z : List ℕ×List ℕ => decide (z.1=z.2)) :=
  listNatTestRealizer.congr (fun z => Bool.eq_iff_iff.mpr (by simp only [listNatTest_iff,decide_eq_true_eq]))

theorem polynomial_listNatEqual : PolynomialTime listNatEqual :=
  polynomial_congr _ polynomial_listNatTest

def profileCodeEqual : Realizer (fun z : (List ℕ×List ℕ)×(List ℕ×List ℕ) =>
    decide (z.1=z.2)) := pairEqual listNatEqual listNatEqual

theorem polynomial_profileCodeEqual : PolynomialTime profileCodeEqual :=
  polynomial_pairEqual polynomial_listNatEqual polynomial_listNatEqual

def profileCodeDedup : Realizer (List.dedup (α := List ℕ×List ℕ)) := dedup profileCodeEqual

theorem polynomial_profileCodeDedup : PolynomialTime profileCodeDedup :=
  polynomial_dedup polynomial_profileCodeEqual

end ContingencyTables.ProfilePrograms

end OAI
