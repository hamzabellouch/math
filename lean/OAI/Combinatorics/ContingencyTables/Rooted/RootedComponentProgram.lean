import OAI.Combinatorics.ContingencyTables.Rooted.RootedRootPenalty
import OAI.Combinatorics.ContingencyTables.Rooted.ForestAffineProgram

namespace OAI

/-! # Polynomial signed component sums for the executed root labels -/

namespace ContingencyTables.RootedComponentProgram

open MatchingFPRAS.TreeTyped Polynomial
open scoped BigOperators Classical

abbrev Record := ℕ×(ℕ×ℕ)
abbrev Input := ℕ×List Record

def positiveTerm (z : ℕ×Record) : ℕ := if z.1=z.2.1 then z.2.2.1 else 0
def negativeTerm (z : ℕ×Record) : ℕ := if z.1=z.2.1 then z.2.2.2 else 0

def positiveTermRealizer : Realizer positiveTerm :=
  (choose (composition (pair first (composition second first)) natEqual)
    (composition (composition second second) first) (constant 0)).congr (by
      intro z
      simp only [Function.comp_apply,decide_eq_true_eq,positiveTerm])

def negativeTermRealizer : Realizer negativeTerm :=
  (choose (composition (pair first (composition second first)) natEqual)
    (composition (composition second second) second) (constant 0)).congr (by
      intro z
      simp only [Function.comp_apply,decide_eq_true_eq,negativeTerm])

lemma polynomial_positiveTerm : PolynomialTime positiveTermRealizer :=
  polynomial_congr _ (polynomial_choose
    (polynomial_composition (polynomial_pair polynomial_first
      (polynomial_composition polynomial_second polynomial_first)) polynomial_natEqual)
    (polynomial_composition (polynomial_composition polynomial_second polynomial_second)
      polynomial_first) (polynomial_constant 0))

lemma polynomial_negativeTerm : PolynomialTime negativeTermRealizer :=
  polynomial_congr _ (polynomial_choose
    (polynomial_composition (polynomial_pair polynomial_first
      (polynomial_composition polynomial_second polynomial_first)) polynomial_natEqual)
    (polynomial_composition (polynomial_composition polynomial_second polynomial_second)
      polynomial_second) (polynomial_constant 0))

def parts (z : Input) : ℕ×ℕ :=
  ((z.2.map (fun r => positiveTerm (z.1,r))).sum,
    (z.2.map (fun r => negativeTerm (z.1,r))).sum)

def partsRealizer : Realizer parts :=
  pair (composition (mapWith positiveTermRealizer) listSum)
    (composition (mapWith negativeTermRealizer) listSum)

lemma polynomial_parts : PolynomialTime partsRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_mapWith polynomial_positiveTerm) polynomial_listSum)
    (polynomial_composition (polynomial_mapWith polynomial_negativeTerm) polynomial_listSum)

def absoluteDifference (z : ℕ×ℕ) : ℕ := z.1-z.2+(z.2-z.1)

def absoluteDifferenceRealizer : Realizer absoluteDifference :=
  composition (pair subtract (composition (pair second first) subtract)) add

lemma polynomial_absoluteDifference : PolynomialTime absoluteDifferenceRealizer :=
  polynomial_composition (polynomial_pair polynomial_subtract
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_subtract))
    polynomial_add

lemma absoluteDifference_eq (p q : ℕ) : absoluteDifference (p,q)=( (p:ℤ)-q).natAbs := by
  rcases Nat.le_total p q with hpq|hqp
  · rw [Int.natAbs_natCast_sub_natCast_of_le hpq]
    simp [absoluteDifference,Nat.sub_eq_zero_of_le hpq]
  · rw [Int.natAbs_natCast_sub_natCast_of_ge hqp]
    simp [absoluteDifference,Nat.sub_eq_zero_of_le hqp]

def component (z : Input) : ℕ := absoluteDifference (parts z)
def componentRealizer : Realizer component := composition partsRealizer absoluteDifferenceRealizer

lemma polynomial_component : PolynomialTime componentRealizer :=
  polynomial_composition polynomial_parts polynomial_absoluteDifference

def total (rs : List Record) : ℕ :=
  ((List.range rs.length).map (fun a => component (a,rs))).sum

def totalRealizer : Realizer total :=
  composition (composition (pair identity (composition listLength range))
    (mapWith (composition (pair second first) componentRealizer))) listSum

theorem polynomial_total : PolynomialTime totalRealizer := by
  have hr : PolynomialTime (composition (listLength (A := Record)) range) := by
    apply polynomial_boundedRange polynomial_listLength X
    intro rs
    simpa only [Polynomial.eval_X] using list_length_le_weight rs
  exact polynomial_composition
    (polynomial_composition (polynomial_pair polynomial_identity hr)
      (polynomial_mapWith (polynomial_composition
        (polynomial_pair polynomial_second polynomial_first) polynomial_component))) polynomial_listSum

def records {n : ℕ} (root : Fin n → Fin n) (p q : Fin n → ℕ) : List Record :=
  List.ofFn (fun i => ((root i).val,(p i,q i)))

lemma parts_records {n : ℕ} (root : Fin n → Fin n) (p q : Fin n → ℕ) (a : Fin n) :
    ((parts (a.val,records root p q)).1:ℤ)-(parts (a.val,records root p q)).2=
      ∑ i,if root i=a then (p i:ℤ)-q i else 0 := by
  simp only [parts,records,List.map_ofFn,Function.comp_apply,positiveTerm,negativeTerm,
    List.sum_ofFn,Nat.cast_sum]
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : root i=a
  · simp [h]
  · have hval : a.val≠(root i).val := by
      intro he
      exact h (Fin.ext he.symm)
    simp [h,hval]

theorem component_records {n : ℕ} (root : Fin n → Fin n) (p q : Fin n → ℕ) (a : Fin n) :
    component (a.val,records root p q)=(∑ i,if root i=a then (p i:ℤ)-q i else 0).natAbs := by
  rw [component,absoluteDifference_eq,parts_records]

theorem total_records {n : ℕ} (root : Fin n → Fin n) (p q : Fin n → ℕ) :
    total (records root p q)=∑ a,(∑ i,if root i=a then (p i:ℤ)-q i else 0).natAbs := by
  have he : (List.range n).map (fun a => component (a,records root p q))=
      List.ofFn (fun a : Fin n => component (a.val,records root p q)) := by
    apply List.ext_getElem
    · simp only [List.length_map,List.length_range,List.length_ofFn]
    · intro i hi _
      simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
  unfold total
  rw [show (records root p q).length=n by simp only [records,List.length_ofFn]]
  rw [he,List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro a _
  exact component_records root p q a

end ContingencyTables.RootedComponentProgram

end OAI
