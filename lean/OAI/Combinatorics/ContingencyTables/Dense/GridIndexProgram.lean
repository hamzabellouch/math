import OAI.Combinatorics.ContingencyTables.Transport.FiniteGridWords
import OAI.Combinatorics.ContingencyTables.Transport.AxisProposalTest

namespace OAI

/-! # Binary indexing into the explicitly enumerated grid -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary
open scoped BigOperators

abbrev GridIndexData := List ℕ×ℕ

def gridIndexPowerInput (z : GridIndexData×ℕ) : GridEnumerationData×ℕ :=
  (((z.1.1.map (fun _ => false)),z.1.2),z.2)

def gridIndexPowerInputRealizer : Realizer gridIndexPowerInput :=
  pair (pair (composition (composition first first) (map (constant false)))
    (composition first second)) second

lemma polynomial_gridIndexPowerInput : PolynomialTime gridIndexPowerInputRealizer :=
  polynomial_pair (polynomial_pair (polynomial_composition
    (polynomial_composition polynomial_first polynomial_first)
    (polynomial_map (polynomial_constant false)))
    (polynomial_composition polynomial_first polynomial_second)) polynomial_second

def gridIndexTerm (z : GridIndexData×ℕ) : ℕ :=
  z.1.1.getD z.2 0*clippedGridPower (gridIndexPowerInput z)

def gridIndexTermRealizer : Realizer gridIndexTerm := by
  let val : Realizer (fun z : GridIndexData×ℕ => z.1.1.getD z.2 0) :=
    composition (pair (composition first first) second) (getDFast 0)
  let power := composition gridIndexPowerInputRealizer clippedGridPowerRealizer
  let result := composition (pair val power) multiply
  exact result

lemma polynomial_gridIndexTerm : PolynomialTime gridIndexTermRealizer := by
  unfold gridIndexTermRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      (polynomial_getDFast 0))
    (polynomial_composition polynomial_gridIndexPowerInput polynomial_clippedGridPower))
    polynomial_multiply

def gridIndexIndices (z : GridIndexData) : List ℕ := List.range z.1.length

def gridIndexIndicesRealizer : Realizer gridIndexIndices :=
  composition (composition first listLength) range

lemma polynomial_gridIndexIndices : PolynomialTime gridIndexIndicesRealizer := by
  apply polynomial_boundedRange (polynomial_composition polynomial_first polynomial_listLength)
    Polynomial.X
  intro z
  simpa only [Function.comp_apply,Polynomial.eval_X] using
    (list_length_le_weight z.1).trans (weight_fst z)

def gridIndex (z : GridIndexData) : ℕ :=
  ((gridIndexIndices z).map (fun i => gridIndexTerm (z,i))).sum

def gridIndexRealizer : Realizer gridIndex :=
  composition (composition (pair identity gridIndexIndicesRealizer)
    (mapWith gridIndexTermRealizer)) listSum

/-- Index computation is polynomial in the binary grid coordinates and
base; the exponent loops are bounded by the coordinate list length. -/
theorem polynomial_gridIndex : PolynomialTime gridIndexRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_identity polynomial_gridIndexIndices)
    (polynomial_mapWith polynomial_gridIndexTerm)) polynomial_listSum

private lemma range_sum (f : ℕ → ℕ) (q : ℕ) :
    ((List.range q).map f).sum=∑ j : Fin q,f j.val := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [List.sum_range_succ,Fin.sum_univ_castSucc,ih]
    rfl

lemma gridIndex_ofFn {q K : ℕ} (f : Fin q → Fin K) :
    gridIndex (List.ofFn (fun i => (f i).val),K)=(finFunctionFinEquiv f).val := by
  unfold gridIndex gridIndexIndices
  rw [List.length_ofFn,range_sum,finFunctionFinEquiv_apply]
  apply Finset.sum_congr rfl
  intro i _
  unfold gridIndexTerm gridIndexPowerInput clippedGridPower clippedGridPowerInput
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt,List.length_map,
    List.length_ofFn,BinaryPowerPrograms.power_eq,dite_true,Option.getD_some]
  rw [min_eq_left (Nat.le_of_lt i.isLt)]

/-- The computed integer is exactly the position used by the state list. -/
theorem gridIndex_code {q K : ℕ} (a : Grid (I := Fin q) K) :
    gridIndex (gridNatCode a,K)=((gridEnumeration q K).symm a).val := by
  let f : Fin q → Fin K := fun i => (gridDigitEquiv K).symm (a i)
  have hcode : gridNatCode a=List.ofFn (fun i => (f i).val) := rfl
  rw [hcode,gridIndex_ofFn]
  rfl

end ContingencyTables.DensePrograms

end OAI
