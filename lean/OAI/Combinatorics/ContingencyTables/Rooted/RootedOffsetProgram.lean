import OAI.Combinatorics.ContingencyTables.Rooted.RootedCoefficientProgram

namespace OAI

/-! # Computing the forest affine offset from the stored cell values

Every summand uses the executed cut flags and coefficient. The input
contains the baseline and the two stored views, rather than an affine
offset supplied by an oracle.
-/

namespace ContingencyTables.RootedOffsetProgram

open MatchingFPRAS.TreeTyped SignedPairProgram
open scoped BigOperators Classical

abbrev WeightedInput := (ℕ×ℕ)×(Signed×Signed)
abbrev Entry := (RootedCoefficientProgram.Input×(Signed×Signed))×Signed
abbrev Input := Signed×List Entry

def weightedDifference (z : WeightedInput) : Signed :=
  minus (times ((z.1.1,0),z.2.1),times ((z.1.2,0),z.2.2))

def weightedDifferenceRealizer : Realizer weightedDifference :=
  composition (pair
    (composition (pair (pair (composition first first) (constant 0))
      (composition second first)) timesRealizer)
    (composition (pair (pair (composition first second) (constant 0))
      (composition second second)) timesRealizer)) minusRealizer

lemma polynomial_weightedDifference : PolynomialTime weightedDifferenceRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
        (polynomial_constant 0))
      (polynomial_composition polynomial_second polynomial_first)) polynomial_times)
    (polynomial_composition (polynomial_pair
      (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
        (polynomial_constant 0))
      (polynomial_composition polynomial_second polynomial_second)) polynomial_times))
    polynomial_minus

lemma value_weightedDifference (z : WeightedInput) :
    value (weightedDifference z)=(z.1.1:ℤ)*value z.2.1-(z.1.2:ℤ)*value z.2.2 := by
  rw [weightedDifference,value_minus,value_times,value_times]
  rfl

lemma value_parts (z : ℤ) : value (ForestAffineProgram.signedParts z)=z :=
  ForestAffineProgram.signedParts_sub z

def cellInput (z : Entry) : RootedCoefficientProgram.Input := z.1.1
def cellInputRealizer : Realizer cellInput := composition first first
lemma polynomial_cellInput : PolynomialTime cellInputRealizer :=
  polynomial_composition polynomial_first polynomial_first

def shifted (z : Entry) : Signed×Signed :=
  (minus (z.1.2.1,z.2),minus (z.1.2.2,z.2))
def shiftedRealizer : Realizer shifted :=
  pair
    (composition (f := fun z : Entry => (z.1.2.1,z.2)) (g := SignedPairProgram.minus)
      (pair (composition (composition first second) first) second) minusRealizer)
    (composition (f := fun z : Entry => (z.1.2.2,z.2)) (g := SignedPairProgram.minus)
      (pair (composition (composition first second) second) second) minusRealizer)
lemma polynomial_shifted : PolynomialTime shiftedRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
        polynomial_first) polynomial_second) polynomial_minus)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
        polynomial_second) polynomial_second) polynomial_minus)

def cutTerm (z : Entry) : Signed :=
  weightedDifference (RootedCoefficientProgram.signs (cellInput z).1,shifted z)
def cutTermRealizer : Realizer cutTerm :=
  composition (pair (composition (composition cellInputRealizer first)
    RootedCoefficientProgram.signsRealizer) shiftedRealizer) weightedDifferenceRealizer
lemma polynomial_cutTerm : PolynomialTime cutTermRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_cellInput polynomial_first)
      RootedCoefficientProgram.polynomial_signs) polynomial_shifted) polynomial_weightedDifference

def smallTest (z : Entry) : Bool := !decide ((cellInput z).2.1 ≤ (cellInput z).2.2)
def smallTestRealizer : Realizer smallTest :=
  composition (composition (composition cellInputRealizer second) leNat) boolNot
lemma polynomial_smallTest : PolynomialTime smallTestRealizer :=
  polynomial_composition
    (polynomial_composition (polynomial_composition polynomial_cellInput polynomial_second)
      polynomial_leNat) polynomial_boolNot

def smallTerm (z : Entry) : Signed := if smallTest z then cutTerm z else (0,0)
def smallTermRealizer : Realizer smallTerm :=
  choose smallTestRealizer cutTermRealizer (constant (0,0))
lemma polynomial_smallTerm : PolynomialTime smallTermRealizer :=
  polynomial_choose polynomial_smallTest polynomial_cutTerm (polynomial_constant (0,0))

def summand (z : Entry) : Signed :=
  plus (times (smallTerm z,RootedCoefficientProgram.treeSigns (cellInput z).1.1),
    times (RootedCoefficientProgram.coefficient (cellInput z),z.2))
def summandRealizer : Realizer summand :=
  composition (pair
    (composition (pair smallTermRealizer
      (composition (composition (composition cellInputRealizer first) first)
        RootedCoefficientProgram.treeSignsRealizer)) timesRealizer)
    (composition (pair (composition cellInputRealizer
      RootedCoefficientProgram.coefficientRealizer) second) timesRealizer)) plusRealizer
lemma polynomial_summand : PolynomialTime summandRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_smallTerm
      (polynomial_composition
        (polynomial_composition (polynomial_composition polynomial_cellInput polynomial_first)
          polynomial_first) RootedCoefficientProgram.polynomial_treeSigns)) polynomial_times)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_cellInput RootedCoefficientProgram.polynomial_coefficient)
      polynomial_second) polynomial_times)) polynomial_plus

def offset (z : Input) : Signed :=
  SignedPairProgram.normalize (minus (z.1,sum (z.2.map summand)))
def offsetRealizer : Realizer offset :=
  composition (f := fun z : Input => minus (z.1,sum (z.2.map summand)))
    (g := SignedPairProgram.normalize)
    (composition (f := fun z : Input => (z.1,sum (z.2.map summand))) (g := SignedPairProgram.minus)
      (pair first (composition (composition second (map summandRealizer)) sumRealizer)) minusRealizer)
    normalizeRealizer
theorem polynomial_offset : PolynomialTime offsetRealizer :=
  polynomial_composition (polynomial_composition (polynomial_pair
    polynomial_first
    (polynomial_composition (polynomial_composition polynomial_second
      (polynomial_map polynomial_summand)) polynomial_sum)) polynomial_minus) polynomial_normalize

lemma value_offset (z : Input) :
    value (offset z)=value z.1-(z.2.map (fun e => value (summand e))).sum := by
  rw [offset,value_normalize,value_minus,value_sum]
  simp only [List.map_map,Function.comp_def]

open CompanionFactorialApplication RootedCompletion RootedIntegerEvaluation

noncomputable def entry {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (t : GraphCompletionCounts.TreeCell A.T) (x q : Fin m → Fin n → ℤ)
    (a : Fin m×Fin n) : Entry :=
  ((RootedCoefficientProgram.input A t a,
    (ForestAffineProgram.signedParts (x a.1 a.2),ForestAffineProgram.signedParts (q a.1 a.2))),
    ForestAffineProgram.signedParts (A.X a.1 a.2))

lemma smallTest_entry {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (t : GraphCompletionCounts.TreeCell A.T) (x q : Fin m → Fin n → ℤ)
    (a : Fin m×Fin n) : smallTest (entry A t x q a)=A.small a.1 a.2 := by
  unfold smallTest cellInput entry RootedCoefficientProgram.input
  cases hs : A.small a.1 a.2 with
  | false => simp [(A.hlarge _ _ hs).1]
  | true => simp [Nat.not_le.mpr (A.hsmall _ _ hs)]

lemma cutTerm_entry {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (t : GraphCompletionCounts.TreeCell A.T) (x q : Fin m → Fin n → ℤ)
    (a : Fin m×Fin n) : value (cutTerm (entry A t x q a))=
      integerIndicator (RootedCut.treeCut A.T (rowColumn A.T) t (.inl a.1))*(x a.1 a.2-A.X a.1 a.2)-
      integerIndicator (RootedCut.treeCut A.T (rowColumn A.T) t (.inr a.2))*(q a.1 a.2-A.X a.1 a.2) := by
  rw [cutTerm,value_weightedDifference]
  dsimp only [shifted,entry,cellInput]
  rw [value_minus,value_minus]
  simp only [value_parts]
  unfold RootedCoefficientProgram.signs RootedCoefficientProgram.input
  rw [RootedCutReindex.canonicalCut_treeCut,RootedCutReindex.canonicalCut_treeCut]
  cases hr : RootedCut.treeCut A.T (rowColumn A.T) t (.inl a.1) <;>
    cases hc : RootedCut.treeCut A.T (rowColumn A.T) t (.inr a.2) <;>
    simp [RootedCoefficientProgram.bit,integerIndicator]

lemma summand_entry {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (t : GraphCompletionCounts.TreeCell A.T) (x q : Fin m → Fin n → ℤ)
    (a : Fin m×Fin n) : value (summand (entry A t x q a))=
      (if A.small a.1 a.2 then
        integerIndicator (RootedCut.treeCut A.T (rowColumn A.T) t (.inl a.1))*(x a.1 a.2-A.X a.1 a.2)-
          integerIndicator (RootedCut.treeCut A.T (rowColumn A.T) t (.inr a.2))*(q a.1 a.2-A.X a.1 a.2)
        else 0)*sign A (rowColumn A.T) t t.val+
        RootedIntegerEvaluation.coefficient A (rowColumn A.T) t a*A.X a.1 a.2 := by
  rw [summand,value_plus,value_times,value_times]
  have ht := RootedCoefficientProgram.treeSigns_input A t a
  have hc := RootedCoefficientProgram.coefficient_input A t a
  have hb : value (entry A t x q a).2=(A.X a.1 a.2:ℤ) := by
    exact value_parts _
  have hs : value (smallTerm (entry A t x q a))=
      if A.small a.1 a.2 then
        integerIndicator (RootedCut.treeCut A.T (rowColumn A.T) t (.inl a.1))*(x a.1 a.2-A.X a.1 a.2)-
          integerIndicator (RootedCut.treeCut A.T (rowColumn A.T) t (.inr a.2))*(q a.1 a.2-A.X a.1 a.2)
        else 0 := by
    rw [smallTerm,smallTest_entry]
    split_ifs
    · exact cutTerm_entry A t x q a
    · rfl
  rw [hs,hb]
  rw [show (cellInput (entry A t x q a))=RootedCoefficientProgram.input A t a by rfl,ht,hc]

noncomputable def data {m n N : ℕ} (A : Instance (Fin m) (Fin n))
    (t : GraphCompletionCounts.TreeCell A.T) (x q : Fin m → Fin n → ℤ)
    (e : Fin N ≃ Fin m×Fin n) : Input :=
  (ForestAffineProgram.signedParts (A.X t.val.1 t.val.2),
    List.ofFn (fun i => entry A t x q (e i)))

/-- The executed normalized pair is the exact manuscript affine offset. -/
theorem offset_data {m n N : ℕ} (A : Instance (Fin m) (Fin n))
    (t : GraphCompletionCounts.TreeCell A.T) (x q : Fin m → Fin n → ℤ)
    (e : Fin N ≃ Fin m×Fin n) :
    offset (data A t x q e)=ForestAffineProgram.signedParts
      (RootedIntegerEvaluation.offset A (rowColumn A.T) t x q) := by
  have he : (∑ i : Fin N,value (summand (entry A t x q (e i))))=
      ∑ a : Fin m×Fin n,value (summand (entry A t x q a)) :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  rw [offset,normalize_eq]
  congr 1
  rw [value_minus,value_sum]
  simp only [data,List.map_ofFn,Function.comp_apply,List.sum_ofFn,value_parts]
  rw [he]
  simp only [summand_entry]
  rw [Finset.sum_add_distrib,←Finset.sum_mul]
  unfold RootedIntegerEvaluation.offset RootedIntegerEvaluation.smallContribution
  ring

end ContingencyTables.RootedOffsetProgram

end OAI
