import OAI.Combinatorics.ContingencyTables.Machines.SignedPairProgram
import OAI.Combinatorics.ContingencyTables.Rooted.RootedCutReindex

namespace OAI

/-! # Computing signed affine coefficients from the actual forest graph

The tree and cell endpoints are ordinary vertex indices. The program
computes the canonical cut flags, tests the capacity threshold and tree
adjacency, and returns the normalized signed coefficient.
-/

namespace ContingencyTables.RootedCoefficientProgram

open MatchingFPRAS.TreeTyped
open SignedPairProgram FiniteGraphRootProgram FiniteGraphCutProgram
open scoped Classical

abbrev Input := (EdgeInput×(ℕ×ℕ))×(ℕ×ℕ)

def bit (b : Bool) : ℕ := if b then 1 else 0

def bitRealizer : Realizer bit := choose identity (constant 1) (constant 0)
lemma polynomial_bit : PolynomialTime bitRealizer :=
  polynomial_choose polynomial_identity (polynomial_constant 1) (polynomial_constant 0)

def signs (z : EdgeInput×(ℕ×ℕ)) : Signed :=
  (bit (canonicalCutCode (z.1,z.2.1)),bit (canonicalCutCode (z.1,z.2.2)))

def signsRealizer : Realizer signs :=
  pair
    (composition (composition (pair first (composition second first)) canonicalCutCodeRealizer)
      bitRealizer)
    (composition (composition (pair first (composition second second)) canonicalCutCodeRealizer)
      bitRealizer)

lemma polynomial_signs : PolynomialTime signsRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_composition (polynomial_pair polynomial_first
      (polynomial_composition polynomial_second polynomial_first)) polynomial_canonicalCutCode)
      polynomial_bit)
    (polynomial_composition (polynomial_composition (polynomial_pair polynomial_first
      (polynomial_composition polynomial_second polynomial_second)) polynomial_canonicalCutCode)
      polynomial_bit)

def treeSigns (z : EdgeInput) : Signed := signs (z,z.2)
def treeSignsRealizer : Realizer treeSigns := composition (pair identity second) signsRealizer
lemma polynomial_treeSigns : PolynomialTime treeSignsRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_second) polynomial_signs

def adjacent (z : GraphCode×(ℕ×ℕ)) : Bool := decide (z.2.2 ∈ z.1.getD z.2.1 [])
def adjacentRealizer : Realizer adjacent :=
  composition (pair (composition (pair first (composition second first)) (getDFast []))
    (composition second second)) membership
lemma polynomial_adjacent : PolynomialTime adjacentRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_first
      (polynomial_composition polynomial_second polynomial_first)) (polynomial_getDFast []))
    (polynomial_composition polynomial_second polynomial_second)) polynomial_membership

def freeTest (z : Input) : Bool :=
  decide (z.2.1 ≤ z.2.2) && !adjacent (z.1.1.1,z.1.2)

def freeTestRealizer : Realizer freeTest :=
  composition (pair (composition second leNat)
    (composition (composition (pair (composition (composition first first) first)
      (composition first second)) adjacentRealizer) boolNot)) boolAnd

lemma polynomial_freeTest : PolynomialTime freeTestRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_second polynomial_leNat)
    (polynomial_composition (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
      (polynomial_composition polynomial_first polynomial_second)) polynomial_adjacent)
      polynomial_boolNot)) polynomial_boolAnd

def coefficient (z : Input) : Signed :=
  if freeTest z then SignedPairProgram.normalize (neg (times (signs z.1,treeSigns z.1.1))) else (0,0)

def coefficientRealizer : Realizer coefficient :=
  choose freeTestRealizer
    (composition (composition (composition (pair (composition first signsRealizer)
      (composition (composition first first) treeSignsRealizer)) timesRealizer) negRealizer)
      normalizeRealizer)
    (constant (0,0))

lemma polynomial_coefficient : PolynomialTime coefficientRealizer :=
  polynomial_choose polynomial_freeTest
    (polynomial_composition (polynomial_composition (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_signs)
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_treeSigns)) polynomial_times) polynomial_neg) polynomial_normalize)
    (polynomial_constant (0,0))

lemma adjacent_graph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) : adjacent (graphCode G,(u.val,v.val))=decide (G.Adj u v) := by
  apply Bool.eq_iff_iff.mpr
  simp only [adjacent,decide_eq_true_eq,graphCode_getD,adjacencyRow_mem]
  constructor
  · rintro ⟨w,hw,he⟩
    have hwu : w=v := Fin.ext hw
    subst w
    exact G.adj_symm he
  · intro h
    exact ⟨v,rfl,G.adj_symm h⟩

open CompanionFactorialApplication RootedCompletion RootedIntegerEvaluation

noncomputable def input {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (t : GraphCompletionCounts.TreeCell A.T) (a : Fin m×Fin n) : Input :=
  (((graphCode (A.T.comap finSumFinEquiv.symm),
      ((finSumFinEquiv (m := m) (n := n) (.inl t.val.1)).val,(finSumFinEquiv (m := m) (n := n) (.inr t.val.2)).val)),
      ((finSumFinEquiv (m := m) (n := n) (.inl a.1)).val,(finSumFinEquiv (m := m) (n := n) (.inr a.2)).val)),
    (A.W,A.b a.1 a.2))

lemma signs_input {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (t : GraphCompletionCounts.TreeCell A.T) (a : Fin m×Fin n) :
    value (signs (input A t a).1)=RootedIntegerEvaluation.sign A (rowColumn A.T) t a := by
  unfold signs input
  rw [RootedCutReindex.canonicalCut_treeCut,RootedCutReindex.canonicalCut_treeCut]
  cases hr : RootedCut.treeCut A.T (rowColumn A.T) t (.inl a.1) <;>
    cases hc : RootedCut.treeCut A.T (rowColumn A.T) t (.inr a.2) <;>
    simp [SignedPairProgram.value,bit,RootedIntegerEvaluation.sign,
      RootedIntegerEvaluation.integerIndicator,hr,hc]

lemma treeSigns_input {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (t : GraphCompletionCounts.TreeCell A.T) (a : Fin m×Fin n) :
    value (treeSigns (input A t a).1.1)=RootedIntegerEvaluation.sign A (rowColumn A.T) t t.val := by
  change value (signs (input A t t.val).1)=_
  exact signs_input A t t.val

lemma freeTest_input {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (t : GraphCompletionCounts.TreeCell A.T) (a : Fin m×Fin n) :
    freeTest (input A t a)=decide (A.small a.1 a.2=false ∧ ¬A.T.Adj (.inl a.1) (.inr a.2)) := by
  have hcut : A.W ≤ A.b a.1 a.2 ↔ A.small a.1 a.2=false := by
    cases hs : A.small a.1 a.2 with
    | false => exact ⟨fun _ => rfl,fun _ => (A.hlarge _ _ hs).1⟩
    | true => simp only [Bool.true_eq_false,iff_false]; exact Nat.not_le.mpr (A.hsmall _ _ hs)
  unfold freeTest input
  rw [adjacent_graph]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq,decide_eq_false_iff_not,
    SimpleGraph.comap_adj,Equiv.symm_apply_apply,hcut]

/-- The output is the literal signed coefficient, with no supplied
cut-membership or coefficient-correctness assumption. -/
theorem coefficient_input {m n : ℕ} (A : Instance (Fin m) (Fin n))
    (t : GraphCompletionCounts.TreeCell A.T) (a : Fin m×Fin n) :
    value (coefficient (input A t a))=RootedIntegerEvaluation.coefficient A (rowColumn A.T) t a := by
  unfold coefficient RootedIntegerEvaluation.coefficient
  rw [freeTest_input]
  by_cases h : A.small a.1 a.2=false ∧ ¬A.T.Adj (.inl a.1) (.inr a.2)
  · simp [h,value_normalize,value_neg,value_times,signs_input,treeSigns_input]
  · simp [h,value]

end ContingencyTables.RootedCoefficientProgram

end OAI
