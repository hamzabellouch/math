import OAI.Combinatorics.ContingencyTables.Dense.DenseCompletionProgram
import OAI.Combinatorics.ContingencyTables.Dense.DenseExponentProgram

namespace OAI

/-! # Computing all dense exponent components and their maximum -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ContingencyTables.ProfilePrograms Polynomial
open scoped BigOperators

def listMaximum (z : List ℕ×ℕ) : ℕ := z.1.foldl (fun a b => max b a) z.2

def listMaximumRealizer : Realizer listMaximum := fold maximum

lemma polynomial_maximum : PolynomialTime maximum := by
  unfold maximum
  exact polynomial_congr _ (polynomial_choose polynomial_less polynomial_second polynomial_first)

lemma foldMaximum_size (xs : List ℕ) (a S : ℕ) (ha : a.size≤S)
    (hx : ∀ b∈xs,b.size≤S) :
    (xs.foldl (fun a b => max b a) a).size≤S := by
  induction xs generalizing a with
  | nil => exact ha
  | cons b bs ih =>
    apply ih
    · rcases le_total b a with h|h
      · simpa only [max_eq_right h] using ha
      · simpa only [max_eq_left h] using hx b (by simp)
    · intro c hc
      exact hx c (by simp [hc])

theorem polynomial_listMaximum : PolynomialTime listMaximumRealizer := by
  apply polynomial_fold polynomial_maximum (4*X+1)
  intro xs a pre post he
  let S := weight (xs,a)
  have ha : a.size≤S := (size_le_weight a).trans (weight_snd (xs,a))
  have hb : ∀ b∈pre,b.size≤S := by
    intro b hb
    exact (size_le_weight b).trans ((weight_mem (as := xs) (by simp [he,hb])).trans
      (weight_fst (xs,a)))
  have hs := foldMaximum_size pre a S ha hb
  have hw := weight_nat_le (pre.foldl (fun a b => max b a) a)
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,eval_one]
  change _≤4*S+1
  omega

lemma listMaximum_le (xs : List ℕ) (a M : ℕ) :
    listMaximum (xs,a)≤M ↔ a≤M ∧ ∀ b∈xs,b≤M := by
  induction xs generalizing a with
  | nil => simp [listMaximum]
  | cons b bs ih =>
    simp only [listMaximum,List.foldl_cons] at ih ⊢
    rw [ih]
    simp only [max_le_iff,List.mem_cons]
    constructor
    · rintro ⟨⟨hb,ha⟩,hbs⟩
      refine ⟨ha,?_⟩
      intro c hc
      rcases hc with rfl|hc
      · exact hb
      · exact hbs c hc
    · rintro ⟨ha,hxs⟩
      exact ⟨⟨hxs b (Or.inl rfl),ha⟩,fun c hc => hxs c (Or.inr hc)⟩

lemma le_listMaximum_default (xs : List ℕ) (a : ℕ) : a≤listMaximum (xs,a) := by
  exact ((listMaximum_le xs a _).mp le_rfl).1

lemma le_listMaximum_member (xs : List ℕ) (a b : ℕ) (hb : b∈xs) :
    b≤listMaximum (xs,a) := ((listMaximum_le xs a _).mp le_rfl).2 b hb

abbrev ExponentData := CompletionData×ℕ

def exponentCellData (z : ExponentData×(ℕ×ℕ)) : ComponentData :=
  ((z.1.2,min (z.1.1.1.1.getD z.2.1 0) (z.1.1.1.2.getD z.2.2 0)),
    completionParts (z.1.1,z.2))

def exponentCellDataRealizer : Realizer exponentCellData := by
  let R : Realizer (fun z : ExponentData×(ℕ×ℕ) => z.1.1.1.1) :=
    composition (composition (composition first first) first) first
  let C : Realizer (fun z : ExponentData×(ℕ×ℕ) => z.1.1.1.2) :=
    composition (composition (composition first first) first) second
  let I : Realizer (fun z : ExponentData×(ℕ×ℕ) => z.2.1) := composition second first
  let J : Realizer (fun z : ExponentData×(ℕ×ℕ) => z.2.2) := composition second second
  exact pair (pair (composition first second)
    (composition (pair (composition (pair R I) (getDFast 0))
      (composition (pair C J) (getDFast 0))) minimum))
    (composition (pair (composition first first) second) completionPartsRealizer)

theorem polynomial_exponentCellData : PolynomialTime exponentCellDataRealizer := by
  unfold exponentCellDataRealizer
  apply polynomial_pair
  · apply polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    apply polynomial_composition _ polynomial_minimum
    apply polynomial_pair
    · apply polynomial_composition _ (polynomial_getDFast 0)
      exact polynomial_pair (polynomial_composition
        (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
          polynomial_first) polynomial_first)
        (polynomial_composition polynomial_second polynomial_first)
    · apply polynomial_composition _ (polynomial_getDFast 0)
      exact polynomial_pair (polynomial_composition
        (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
          polynomial_first) polynomial_second)
        (polynomial_composition polynomial_second polynomial_second)
  · exact polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      polynomial_completionParts

def exponentCell (z : ExponentData×(ℕ×ℕ)) : ℕ := componentValue (exponentCellData z)

def exponentCellRealizer : Realizer exponentCell :=
  composition exponentCellDataRealizer componentRealizer

theorem polynomial_exponentCell : PolynomialTime exponentCellRealizer :=
  polynomial_composition polynomial_exponentCellData polynomial_component

def exponentCells (z : ExponentData) : List (ℕ×ℕ) := cellPairs z.1.1

def exponentCellsRealizer : Realizer exponentCells :=
  composition (composition first first) cellPairsRealizer

theorem polynomial_exponentCells : PolynomialTime exponentCellsRealizer :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_cellPairs

def exponentValues (z : ExponentData) : List ℕ :=
  (exponentCells z).map (fun ij => exponentCell (z,ij))

def exponentValuesRealizer : Realizer exponentValues :=
  composition (pair identity exponentCellsRealizer) (mapWith exponentCellRealizer)

theorem polynomial_exponentValues : PolynomialTime exponentValuesRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_exponentCells)
    (polynomial_mapWith polynomial_exponentCell)

def fullExponent (z : ExponentData) : ℕ := listMaximum (exponentValues z,0)

def fullExponentRealizer : Realizer fullExponent :=
  composition (pair exponentValuesRealizer (constant 0)) listMaximumRealizer

/-- The exponent evaluation traverses only the supplied matrix dimensions. -/
theorem polynomial_fullExponent : PolynomialTime fullExponentRealizer :=
  polynomial_composition (polynomial_pair polynomial_exponentValues (polynomial_constant 0))
    polynomial_listMaximum

end ContingencyTables.DensePrograms

end OAI
