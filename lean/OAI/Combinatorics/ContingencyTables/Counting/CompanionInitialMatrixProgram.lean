import OAI.Combinatorics.ContingencyTables.Counting.CompanionLabelMetadataProgram
import OAI.Combinatorics.ContingencyTables.Counting.CompanionMultiplierMatrixProgram

namespace OAI

/-! # Executing the initial canonical multiplier matrix -/

namespace ContingencyTables.CompanionInitialMatrixProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped CompanionMultiplierMatrixProgram

abbrev Metadata := ℕ × ℕ

def numerator (z : Metadata × Metadata) : ℕ := 6*(z.1.2+1)
def numeratorRealizer : Realizer numerator :=
  composition (f := fun z : Metadata × Metadata => (6,z.1.2+1))
    (g := fun p : ℕ × ℕ => p.1*p.2)
    (pair (constant 6) (composition (composition first second) successor)) multiply
lemma polynomial_numerator : PolynomialTime numeratorRealizer :=
  polynomial_composition (polynomial_pair (polynomial_constant 6)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      polynomial_successor)) polynomial_multiply

def denominator (z : Metadata × Metadata) : ℕ := z.2.2+2
def denominatorRealizer : Realizer denominator :=
  composition (f := fun z : Metadata × Metadata => (z.2.2,2))
    (g := fun p : ℕ × ℕ => p.1+p.2)
    (pair (composition second second) (constant 2)) add
lemma polynomial_denominator : PolynomialTime denominatorRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_second polynomial_second)
    (polynomial_constant 2)) polynomial_add

def sameCell (z : Metadata × Metadata) : Bool := decide (z.1.1=z.2.1)
def sameCellRealizer : Realizer sameCell :=
  composition (pair (composition first first) (composition second first)) natEqual
lemma polynomial_sameCell : PolynomialTime sameCellRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_composition polynomial_second polynomial_first)) polynomial_natEqual

def entry (z : Metadata × Metadata) : TreeFraction.Fraction :=
  if sameCell z then (6,1) else TreeFraction.normalize (numerator z,denominator z)
def entryRealizer : Realizer entry :=
  choose sameCellRealizer (constant (6,1))
    (composition (pair numeratorRealizer denominatorRealizer) TreeFraction.normalizeRealizer)
lemma polynomial_entry : PolynomialTime entryRealizer :=
  polynomial_choose polynomial_sameCell (polynomial_constant (6,1))
    (polynomial_composition (polynomial_pair polynomial_numerator polynomial_denominator)
      TreeFraction.polynomial_normalize)

def row (z : List Metadata × Metadata) : List TreeFraction.Fraction :=
  z.1.map (fun b => entry (z.2,b))
def rowRealizer : Realizer row := composition (pair second first) (mapWith entryRealizer)
lemma polynomial_row : PolynomialTime rowRealizer :=
  polynomial_composition (polynomial_pair polynomial_second polynomial_first)
    (polynomial_mapWith polynomial_entry)

def matrix (xs : List Metadata) : FractionMatrix := xs.map (fun a => row (xs,a))
def matrixRealizer : Realizer matrix := composition (pair identity identity) (mapWith rowRealizer)
lemma polynomial_matrix : PolynomialTime matrixRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_identity)
    (polynomial_mapWith polynomial_row)

def output (z : PairedProfileProgram.Input) : FractionMatrix :=
  matrix (CompanionLabelMetadataProgram.output z)
def outputRealizer : Realizer output :=
  composition (f := CompanionLabelMetadataProgram.output) (g := matrix)
    CompanionLabelMetadataProgram.outputRealizer matrixRealizer
theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition CompanionLabelMetadataProgram.polynomial_output polynomial_matrix

lemma entry_val (a b : Metadata) :
    TreeFraction.val (entry (a,b))=
      if a.1=b.1 then 6 else 6*((a.2:ℚ)+1)/((b.2:ℚ)+2) := by
  unfold entry sameCell
  by_cases h : a.1=b.1
  · simp only [h,decide_true,ite_true,TreeFraction.val,Nat.cast_ofNat,Nat.cast_one,div_one]
  · simp only [h,decide_false,Bool.false_eq_true,ite_false]
    rw [TreeFraction.normalize_val]
    simp only [TreeFraction.val,numerator,denominator,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]

lemma matrix_ofFn {p : ℕ} (f : Fin p → Metadata) :
    matrix (List.ofFn f)=matrixCode (fun i j => entry (f i,f j)) := by
  simp only [matrix,row,matrixCode,List.map_ofFn,Function.comp_def]

noncomputable section
open CanonicalInitialEncoding InitialTransversals CompanionArithmeticProposal
open CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionRationalUpdates TwoLiftStates
open scoped Classical

variable {q : ℕ} (b : Fin q → ℕ)

def metadataAt (i : Fin (CanonicalInitialEncoding.copyOrder b).length) : Metadata :=
  ((PairedCatalogProgram.labelOrder b i).1.val,b (PairedCatalogProgram.labelOrder b i).1)

lemma metadata_code (S : Set (Copy b × Bool)) :
    CompanionLabelMetadataProgram.output (List.ofFn b,encodeSet (coordinateEquiv b) S)=
      List.ofFn (metadataAt b) := by
  rw [CompanionLabelMetadataProgram.output_encode]
  let f : Copy b → Metadata := fun p => (p.1.val,b p.1)
  change (copyOrder b).map f=List.ofFn (fun i => f ((copyOrder b)[i.val]))
  exact (List.ofFn_getElem_eq_map (copyOrder b) f).symm

theorem output_code (S : Set (Copy b × Bool)) :
    output (List.ofFn b,encodeSet (coordinateEquiv b) S)=
      matrixCode (fun i j => entry (metadataAt b i,metadataAt b j)) := by
  rw [output,metadata_code,matrix_ofFn]

variable {m n : ℕ} (A : Instance (Fin m) (Fin n))

def initialEntries (i j : Fin (CanonicalInitialEncoding.copyOrder (capacities A)).length) : TreeFraction.Fraction :=
  entry (metadataAt (capacities A) i,metadataAt (capacities A) j)

lemma pairLabels_cell (i : Fin (CanonicalInitialEncoding.copyOrder (capacities A)).length) :
    cellOrder A (pairLabels A i).1=(PairedCatalogProgram.labelOrder (capacities A) i).1 := by
  change cellOrder A ((cellOrder A).symm (PairedCatalogProgram.labelOrder (capacities A) i).1)=_
  exact (cellOrder A).apply_symm_apply _

lemma metadata_cell_iff (i j : Fin (CanonicalInitialEncoding.copyOrder (capacities A)).length) :
    (metadataAt (capacities A) i).1=(metadataAt (capacities A) j).1 ↔
      (pairLabels A i).1=(pairLabels A j).1 := by
  constructor
  · intro h
    apply (cellOrder A).injective
    rw [pairLabels_cell,pairLabels_cell]
    exact Fin.ext h
  · intro h
    have he := congrArg (fun s => (cellOrder A s).val) h
    simpa only [pairLabels_cell,metadataAt] using he

lemma metadata_capacity (i : Fin (CanonicalInitialEncoding.copyOrder (capacities A)).length) :
    (metadataAt (capacities A) i).2=A.b (pairLabels A i).1.val.1 (pairLabels A i).1.val.2 := by
  change capacities A (PairedCatalogProgram.labelOrder (capacities A) i).1=_
  rw [←pairLabels_cell]
  unfold capacities
  rw [Equiv.symm_apply_apply]

theorem initialEntries_val (i j : Fin (CanonicalInitialEncoding.copyOrder (capacities A)).length) :
    TreeFraction.val (initialEntries A i j)=
      CompanionRationalUpdates.initial A (pair (pairLabels A i)) (pair (pairLabels A j)) := by
  unfold initialEntries
  rw [entry_val]
  simp only [CompanionRationalUpdates.initial,TwoLiftStates.pair]
  simp only [metadata_cell_iff,metadata_capacity]
  by_cases h : (pairLabels A i).1=(pairLabels A j).1 <;> simp only [h,ite_true,ite_false]

theorem output_physical (S : Set (Labels A × Bool)) :
    output (List.ofFn (capacities A),encodeSet (coordinateOrder A) S)=
      matrixCode (initialEntries A) := by
  rw [encodeSet_reindex,output_code]
  rfl

end
end ContingencyTables.CompanionInitialMatrixProgram

end OAI
