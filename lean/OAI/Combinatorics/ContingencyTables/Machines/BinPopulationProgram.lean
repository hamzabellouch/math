import OAI.Combinatorics.ContingencyTables.Machines.BinIntervalProgram
import OAI.Combinatorics.ContingencyTables.Rooted.RootedCatalogGrid
import OAI.Combinatorics.ContingencyTables.Counting.CompanionCorrectionArithmetic

namespace OAI

/-! # Computing the exact population correction in binary

The program multiplies one interval size and one full-range denominator
per free coordinate. It never lists the integer assignments in a bin.
-/

namespace ContingencyTables.BinPopulationProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators Classical

def factorNumerator (z : BinIntervalProgram.Input) : ℕ :=
  z.1.1*BinIntervalProgram.intervalSize z
def factorNumeratorRealizer : Realizer factorNumerator :=
  composition (f := fun z : BinIntervalProgram.Input =>
    (z.1.1,BinIntervalProgram.intervalSize z)) (g := fun p : ℕ×ℕ => p.1*p.2)
    (pair (composition first first) BinIntervalProgram.intervalSizeRealizer) multiply
lemma polynomial_factorNumerator : PolynomialTime factorNumeratorRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first)
    BinIntervalProgram.polynomial_intervalSize) polynomial_multiply

def numerator (zs : List BinIntervalProgram.Input) : ℕ := (zs.map factorNumerator).prod
def numeratorRealizer : Realizer numerator := composition (map factorNumeratorRealizer) listProd
lemma polynomial_numerator : PolynomialTime numeratorRealizer :=
  polynomial_composition (polynomial_map polynomial_factorNumerator) polynomial_listProd

def denominator (zs : List BinIntervalProgram.Input) : ℕ := (zs.map (fun z => z.1.2)).prod
def denominatorRealizer : Realizer denominator :=
  composition (map (composition first second)) listProd
lemma polynomial_denominator : PolynomialTime denominatorRealizer :=
  polynomial_composition (polynomial_map
    (polynomial_composition polynomial_first polynomial_second)) polynomial_listProd

def output (zs : List BinIntervalProgram.Input) : TreeFraction.Fraction :=
  TreeFraction.normalize (numerator zs,denominator zs)
def outputRealizer : Realizer output :=
  composition (pair numeratorRealizer denominatorRealizer) TreeFraction.normalizeRealizer
theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition (polynomial_pair polynomial_numerator polynomial_denominator)
    TreeFraction.polynomial_normalize

lemma output_ofFn {q : ℕ} (K : ℕ) (N beta : Fin q → ℕ) :
    TreeFraction.val (output (List.ofFn (fun i => ((K,N i),beta i))))=
      (K:ℚ)^q*(∏ i : Fin q,(CompanionOracleDensity.intervalSize K (N i) (beta i):ℚ))/
        ∏ i : Fin q,(N i:ℚ) := by
  rw [output,TreeFraction.normalize_val]
  simp only [numerator,denominator,List.map_ofFn,Function.comp_apply,List.prod_ofFn,
    factorNumerator,BinIntervalProgram.intervalSize_eq,TreeFraction.val,
    Nat.cast_prod,Nat.cast_mul,Nat.cast_pow,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,
    Fintype.card_fin]

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary

noncomputable section
variable {m n : ℕ}

def data (A : Instance (Fin m) (Fin n)) (K : ℕ)
    (v : Grid (I := Fin (CompanionOracleDensity.dimension A)) K) : List BinIntervalProgram.Input :=
  List.ofFn (fun i : Fin (RootedCatalogGrid.freeCount A) =>
    ((K,CompanionOracleDensity.freeRange A (RootedForestCatalog.freeEquiv A i)),
      CompanionOracleDensity.naturalBin A v (RootedForestCatalog.freeEquiv A i)))

theorem output_data (A : Instance (Fin m) (Fin n)) (K : ℕ) (hK : 0<K)
    (v : Grid (I := Fin (CompanionOracleDensity.dimension A)) K) :
    TreeFraction.val (output (data A K v))=
      (K:ℚ)^CompanionOracleDensity.dimension A*
        (CompanionOracleDensity.integerFiber A K hK v).card/
          CompanionOracleDensity.assignmentCount A := by
  rw [data,output_ofFn]
  have hc : RootedCatalogGrid.freeCount A=CompanionOracleDensity.dimension A := by
    simpa only [Fintype.card_fin] using Fintype.card_congr (RootedCatalogGrid.coordinateEquiv A)
  have hp : (∏ i : Fin (RootedCatalogGrid.freeCount A),
      (CompanionOracleDensity.intervalSize K
        (CompanionOracleDensity.freeRange A (RootedForestCatalog.freeEquiv A i))
        (CompanionOracleDensity.naturalBin A v (RootedForestCatalog.freeEquiv A i)):ℚ))=
      ((CompanionOracleDensity.integerFiber A K hK v).card:ℚ) := by
    rw [CompanionOracleDensity.integerFiber_card,Nat.cast_prod]
    apply Fintype.prod_equiv (RootedForestCatalog.freeEquiv A)
    intro i
    have hN : 0<CompanionOracleDensity.freeRange A (RootedForestCatalog.freeEquiv A i) := by
      exact Nat.succ_pos _
    rw [FairBits.fiber_card hK hN
      (CompanionOracleDensity.naturalBin_lt A v _)]
    rfl
  have hd : (∏ i : Fin (RootedCatalogGrid.freeCount A),
      (CompanionOracleDensity.freeRange A (RootedForestCatalog.freeEquiv A i):ℚ))=
      (CompanionOracleDensity.assignmentCount A:ℚ) := by
    rw [CompanionOracleDensity.assignmentCount_eq_prod,Nat.cast_prod]
    exact Fintype.prod_equiv (RootedForestCatalog.freeEquiv A) _ _ (fun _ => rfl)
  rw [hp,hd,hc]

theorem output_integerBin (A : Instance (Fin m) (Fin n)) (K : ℕ) (hK : 0<K)
    (f : FreeIndex A.small A.T A.b) :
    TreeFraction.val (output (data A K (CompanionOracleDensity.integerBin A K hK f)))=
      CompanionOracleDensity.rationalPopulation A K hK f :=
  output_data A K hK _

end
end ContingencyTables.BinPopulationProgram

end OAI
