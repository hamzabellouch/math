import OAI.Combinatorics.ContingencyTables.Machines.NetworkCapacityProgram

namespace OAI

/-! # The actual polynomial binary bounded-table feasibility test -/

namespace ContingencyTables.NetworkFeasibilityProgram

open MatchingFPRAS.TreeTyped NetworkVertexCode NetworkCapacityProgram ResidualGraphProgram
open scoped BigOperators

def sourcePair (z : Input) : SignedPairProgram.Signed :=
  SignedPairProgram.sum ((solve z).getD 0 [])

def sourcePairRealizer : Realizer sourcePair :=
  composition (composition (pair solveRealizer (constant 0)) (getDFast []))
    SignedPairProgram.sumRealizer

lemma polynomial_sourcePair : PolynomialTime sourcePairRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_solve (polynomial_constant 0)) (polynomial_getDFast []))
    SignedPairProgram.polynomial_sum

def inputValues (z : Input) : (ℕ×ℕ)×SignedPairProgram.Signed :=
  ((z.1.1.sum,z.1.2.sum),sourcePair z)

def inputValuesRealizer : Realizer inputValues :=
  pair (pair (composition (composition first first) listSum)
    (composition (composition first second) listSum)) sourcePairRealizer

lemma polynomial_inputValues : PolynomialTime inputValuesRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_listSum)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      polynomial_listSum)) polynomial_sourcePair

def testValues (z : (ℕ×ℕ)×SignedPairProgram.Signed) : Bool :=
  decide (z.1.1=z.1.2) && decide (z.2.1=z.1.1+z.2.2)

def testValuesRealizer : Realizer testValues :=
  composition (pair (composition first natEqual)
    (composition (pair (composition second first)
      (composition (pair (composition first first) (composition second second)) add))
      natEqual)) boolAnd

lemma polynomial_testValues : PolynomialTime testValuesRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_natEqual)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_second polynomial_first)
      (polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_first polynomial_first)
        (polynomial_composition polynomial_second polynomial_second)) polynomial_add))
      polynomial_natEqual)) polynomial_boolAnd

def test (z : Input) : Bool := testValues (inputValues z)
def testRealizer : Realizer test := composition inputValuesRealizer testValuesRealizer

lemma polynomial_test : PolynomialTime testRealizer :=
  polynomial_composition polynomial_inputValues polynomial_testValues

lemma flowCode_row_value {n : ℕ} (f : PublishedEdmondsKarp.Flow n) (s : Fin n) :
    SignedPairProgram.value (SignedPairProgram.sum ((flowCode f).getD s.val []))=
      PublishedEdmondsKarp.value s f := by
  have hr : (flowCode f).getD s.val []=
      List.ofFn (fun v=>ForestAffineProgram.signedParts (f s v)) := by
    simp only [flowCode,List.getD_eq_getElem?_getD,List.getElem?_ofFn,s.isLt,
      dite_true,Option.getD_some,Fin.eta]
  rw [hr,SignedPairProgram.value_sum]
  simp only [List.map_ofFn,Function.comp_def,SignedPairProgram.value,
    ForestAffineProgram.signedParts_sub,List.sum_ofFn,PublishedEdmondsKarp.value]

lemma sourcePair_value {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) :
    SignedPairProgram.value (sourcePair (data r c b))=
      LayeredTableNetwork.value (BoundedTableFeasibility.computedFlow r c b) := by
  unfold sourcePair
  rw [solve_code]
  have hs : (BoundedTableFeasibility.vertices m n (LayeredTableNetwork.source :
      LayeredTableNetwork.Vertex m n)).val=0 := index_vertices _
  rw [←hs,flowCode_row_value]
  exact (BoundedTableFeasibility.pull_value _).symm

lemma test_eq_feasible {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) :
    test (data r c b)=BoundedTableFeasibility.feasibleTest r c b := by
  apply Bool.eq_iff_iff.mpr
  simp only [test,testValues,inputValues,Bool.and_eq_true,decide_eq_true_eq,
    BoundedTableFeasibility.feasibleTest,data,List.sum_ofFn]
  have hv := sourcePair_value r c b
  have he : (sourcePair (data r c b)).1=
      (∑ i,r i)+(sourcePair (data r c b)).2 ↔
      SignedPairProgram.value (sourcePair (data r c b))=∑ i,(r i:ℤ) := by
    unfold SignedPairProgram.value
    rw [←Nat.cast_sum]
    omega
  exact and_congr_right (fun _=>he.trans (by rw [hv]))

theorem test_correct {m n : ℕ} (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) :
    test (data r c b)=true ↔ ∃ X,HasMargins X r c ∧ ∀ i j,X i j≤b i j := by
  rw [test_eq_feasible]
  exact BoundedTableFeasibility.feasibleTest_correct hEK r c b

end ContingencyTables.NetworkFeasibilityProgram

end OAI
