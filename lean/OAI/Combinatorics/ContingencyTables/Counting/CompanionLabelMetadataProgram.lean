import OAI.Combinatorics.ContingencyTables.Machines.PairedFactorialProgram
import OAI.Combinatorics.ContingencyTables.Counting.CompanionComputedProposal
import OAI.Combinatorics.ContingencyTables.Transport.DirectedBFSCode

namespace OAI

/-! # Recovering each paired label's cell and capacity

The multiplicities come from the actual bounded profile blocks. A
large numeric capacity never causes an allocation beyond the supplied
profile code. On a canonical code, the resulting order is exactly the
copy order used by the initializer and arithmetic proposals.
-/

namespace ContingencyTables.CompanionLabelMetadataProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial
open PairedProfileProgram PairedFactorialProgram

abbrev Input := PairedProfileProgram.Input

def indices (z : ℕ × List ℕ) : List ℕ := List.range (pairCount z.2)
def indicesRealizer : Realizer indices :=
  composition (composition second pairCountRealizer) range
lemma polynomial_indices : PolynomialTime indicesRealizer := by
  apply polynomial_boundedRange (polynomial_composition polynomial_second polynomial_pairCount) X
  intro z
  simpa only [Function.comp_apply,eval_X,pairCount] using
    (Nat.div_le_self z.2.length 2).trans ((list_length_le_weight z.2).trans (weight_snd z))

def labelRow (z : ℕ × List ℕ) : List (ℕ × ℕ) :=
  (indices z).map (fun _ => (z.1,pairCount z.2))
def labelRowRealizer : Realizer labelRow :=
  composition (pair identity indicesRealizer)
    (mapWith (pair (composition first first) (composition (composition first second) pairCountRealizer)))
lemma polynomial_labelRow : PolynomialTime labelRowRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_indices)
    (polynomial_mapWith (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_pairCount)))

def rowInput (z : Input × ℕ) : ℕ × List ℕ :=
  (z.2,(rows z.1).getD z.2 [])
def rowInputRealizer : Realizer rowInput :=
  pair second (composition (pair
    (composition (f := fun z : Input × ℕ => z.1) (g := rows) first rowsRealizer)
    second) (getDFast []))
lemma polynomial_rowInput : PolynomialTime rowInputRealizer :=
  polynomial_pair polynomial_second (polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_rows) polynomial_second) (polynomial_getDFast []))

def indexedRow (z : Input × ℕ) : List (ℕ × ℕ) := labelRow (rowInput z)
def indexedRowRealizer : Realizer indexedRow :=
  composition (f := rowInput) (g := labelRow) rowInputRealizer labelRowRealizer
lemma polynomial_indexedRow : PolynomialTime indexedRowRealizer :=
  polynomial_composition polynomial_rowInput polynomial_labelRow

def output (z : Input) : List (ℕ × ℕ) :=
  ((NaturalBlockProgram.indices z).map (fun i => indexedRow (z,i))).flatten
def outputRealizer : Realizer output :=
  composition (composition (pair identity NaturalBlockProgram.indicesRealizer)
    (mapWith indexedRowRealizer)) flatten
theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition (polynomial_composition (polynomial_pair polynomial_identity
    NaturalBlockProgram.polynomial_indices) (polynomial_mapWith polynomial_indexedRow)) polynomial_flatten

lemma labelRow_eq (i : ℕ) (xs : List ℕ) :
    labelRow (i,xs)=List.replicate (xs.length/2) (i,xs.length/2) := by
  simp only [labelRow,indices,pairCount,List.map_const',List.length_range]

noncomputable section
open CanonicalInitialEncoding InitialTransversals PairedProfileSemantics
open CompanionArithmeticProposal CompanionFactorialApplication
open scoped Classical
variable {q : ℕ} (b : Fin q → ℕ)

lemma indexedRow_encode (S : Set (Copy b × Bool)) (i : Fin q) :
    indexedRow ((List.ofFn b,encodeSet (coordinateEquiv b) S),i.val)=
      List.replicate (b i) (i.val,b i) := by
  unfold indexedRow rowInput
  rw [rows_encode]
  have he : (cellRows b S).getD i.val []=interleave (List.ofFn (fun k : Fin (b i) =>
      (if (⟨i,k⟩,false) ∈ S then 1 else 0,if (⟨i,k⟩,true) ∈ S then 1 else 0))) := by
    simp [cellRows,List.getD_eq_getElem?_getD]
  rw [he]
  rw [labelRow_eq,interleave_length,List.length_ofFn]
  simp only [Nat.mul_div_cancel_left _ (by decide : 0 < 2)]

lemma output_encode (S : Set (Copy b × Bool)) :
    output (List.ofFn b,encodeSet (coordinateEquiv b) S)=
      (copyOrder b).map (fun p => (p.1.val,b p.1)) := by
  unfold output NaturalBlockProgram.indices
  rw [List.length_ofFn]
  have he : (List.range q).map (fun i => indexedRow ((List.ofFn b,encodeSet (coordinateEquiv b) S),i))=
      List.ofFn (fun i : Fin q => List.replicate (b i) (i.val,b i)) := by
    conv_rhs => rw [List.ofFn_eq_map]
    rw [DirectedBFSCode.range_eq_map]
    simp only [List.map_map,Function.comp_def]
    change (List.finRange q).map (fun i => indexedRow ((List.ofFn b,encodeSet (coordinateEquiv b) S),i.val)) =
      (List.finRange q).map (fun i => List.replicate (b i) (i.val,b i))
    apply List.map_congr_left
    intro i _
    exact indexedRow_encode b S i
  rw [he]
  simp only [copyOrder,List.sigma,List.map_flatMap,List.map_map,List.ofFn_eq_map,
    List.flatten_eq_flatMap,List.flatMap_map,Function.comp_def,id_eq]
  apply List.flatMap_congr
  intro i _
  simp only [List.map_const',List.length_finRange]

end
end ContingencyTables.CompanionLabelMetadataProgram

end OAI
