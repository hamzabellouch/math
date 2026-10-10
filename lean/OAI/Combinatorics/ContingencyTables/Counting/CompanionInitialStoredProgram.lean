import OAI.Combinatorics.ContingencyTables.Counting.CompanionInitialMatrixProgram
import OAI.Combinatorics.ContingencyTables.Rooted.RootedStoredEstimate
import OAI.Combinatorics.ContingencyTables.Rooted.RootedForestCatalog

namespace OAI

/-! # The literal initial count and stored multiplier matrix

The integer count is the product of the free-cell ranges and the small-cell
ranges. Both lists come from the executed forest and cell catalogs.
-/
namespace ContingencyTables.CompanionInitialStoredProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms

abbrev Input := RootedForestCatalog.Data × PairedProfileProgram.Input

def rangeAt (z : RootedForestCatalog.Data×(ℕ×ℕ)) : ℕ := matrixEntry (z.1.2,z.2)+1
def rangeAtRealizer : Realizer rangeAt :=
  composition (f := fun z : RootedForestCatalog.Data×(ℕ×ℕ) => matrixEntry (z.1.2,z.2))
    (g := Nat.succ)
    (composition (f := fun z : RootedForestCatalog.Data×(ℕ×ℕ) => (z.1.2,z.2))
      (g := matrixEntry) (pair (composition first second) second) matrixEntryRealizer) successor
lemma polynomial_rangeAt : PolynomialTime rangeAtRealizer :=
  polynomial_composition (polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_second) polynomial_second)
    polynomial_matrixEntry) polynomial_successor

def freeRanges (d : RootedForestCatalog.Data) : List ℕ :=
  (RootedForestCatalog.catalog (d,false)).map (fun ij => rangeAt (d,ij))
def freeRangesRealizer : Realizer freeRanges :=
  composition (f := fun d : RootedForestCatalog.Data => (d,RootedForestCatalog.catalog (d,false)))
    (g := fun p : RootedForestCatalog.Data×List (ℕ×ℕ) => p.2.map (fun ij => rangeAt (p.1,ij)))
    (pair identity (composition (f := fun d : RootedForestCatalog.Data => (d,false))
      (g := RootedForestCatalog.catalog) (pair identity (constant false)) RootedForestCatalog.catalogRealizer))
    (mapWith rangeAtRealizer)
lemma polynomial_freeRanges : PolynomialTime freeRangesRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant false))
      RootedForestCatalog.polynomial_catalog)) (polynomial_mapWith polynomial_rangeAt)

def freeProduct (d : RootedForestCatalog.Data) : ℕ := (freeRanges d).prod
def freeProductRealizer : Realizer freeProduct :=
  composition (f := freeRanges) (g := List.prod) freeRangesRealizer listProd
lemma polynomial_freeProduct : PolynomialTime freeProductRealizer :=
  polynomial_composition polynomial_freeRanges polynomial_listProd

def smallProduct (xs : List ℕ) : ℕ := (xs.map Nat.succ).prod
def smallProductRealizer : Realizer smallProduct := composition (map successor) listProd
lemma polynomial_smallProduct : PolynomialTime smallProductRealizer :=
  polynomial_composition (polynomial_map polynomial_successor) polynomial_listProd

def total (z : Input) : TreeFraction.Fraction :=
  (freeProduct z.1*smallProduct z.2.1,1)
def totalRealizer : Realizer total :=
  pair (composition (f := fun z : Input => (freeProduct z.1,smallProduct z.2.1))
    (g := fun p : ℕ×ℕ => p.1*p.2)
    (pair (composition (f := fun z : Input => z.1) (g := freeProduct) first freeProductRealizer)
      (composition (f := fun z : Input => z.2.1) (g := smallProduct)
        (composition second first) smallProductRealizer)) multiply) (constant 1)
lemma polynomial_total : PolynomialTime totalRealizer :=
  polynomial_pair (polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_freeProduct)
    (polynomial_composition (polynomial_composition polynomial_second polynomial_first)
      polynomial_smallProduct)) polynomial_multiply) (polynomial_constant 1)

def output (z : Input) : CompanionMultiplierMatrixProgram.FractionMatrix×TreeFraction.Fraction :=
  (CompanionInitialMatrixProgram.output z.2,total z)
def outputRealizer : Realizer output :=
  pair (composition (f := fun z : Input => z.2) (g := CompanionInitialMatrixProgram.output)
    second CompanionInitialMatrixProgram.outputRealizer) totalRealizer
theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_pair (polynomial_composition polynomial_second
    CompanionInitialMatrixProgram.polynomial_output) polynomial_total

noncomputable section
open CompanionFactorialApplication CompanionComputedInitial ForestAssignmentSplit
open CompanionArithmeticProposal
open scoped BigOperators Classical
variable {m n : ℕ} (A : Instance (Fin m) (Fin n))

def data (S : Set (Labels A×Bool)) : Input :=
  (RootedForestCatalog.data A,(List.ofFn (capacities A),encodeSet (coordinateOrder A) S))

lemma rangeAt_data (ij : Fin m×Fin n) :
    rangeAt (RootedForestCatalog.data A,(ij.1.val,ij.2.val))=A.b ij.1 ij.2+1 := by
  unfold rangeAt RootedForestCatalog.data
  rw [matrixEntry_code]

lemma freeRanges_data : freeRanges (RootedForestCatalog.data A)=
    List.ofFn (fun i => A.b (RootedForestCatalog.freeEquiv A i).val.1
      (RootedForestCatalog.freeEquiv A i).val.2+1) := by
  unfold freeRanges
  conv_lhs => rw [←List.ofFn_get (RootedForestCatalog.catalog (RootedForestCatalog.data A,false))]
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  dsimp only [Function.comp_apply,List.get_eq_getElem]
  have h := RootedForestCatalog.catalogCell_coordinates A false i
  change ((RootedForestCatalog.freeEquiv A i).val.1.val,
    (RootedForestCatalog.freeEquiv A i).val.2.val)=_ at h
  rw [←h]
  exact rangeAt_data A _

theorem total_data (S : Set (Labels A×Bool)) :
    TreeFraction.val (total (data A S))=RootedStoredEstimate.initialTotal A := by
  unfold total data freeProduct smallProduct
  rw [freeRanges_data]
  simp only [List.prod_ofFn,List.map_ofFn,TreeFraction.val,Nat.cast_one,div_one,
    Nat.cast_mul,Nat.cast_prod]
  unfold RootedStoredEstimate.initialTotal
  congr 1
  · exact Fintype.prod_equiv (RootedForestCatalog.freeEquiv A) _ _ (fun _ => rfl)
  · exact Fintype.prod_equiv (cellOrder A).symm _ _ (fun _ => rfl)

theorem output_matrix (S : Set (Labels A×Bool)) :
    (output (data A S)).1=CompanionMultiplierMatrixProgram.matrixCode
      (CompanionInitialMatrixProgram.initialEntries A) :=
  CompanionInitialMatrixProgram.output_physical A S

end
end ContingencyTables.CompanionInitialStoredProgram

end OAI
