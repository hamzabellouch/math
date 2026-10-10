import OAI.Combinatorics.ContingencyTables.Transport.PairedProfileSemantics
import OAI.Combinatorics.ContingencyTables.Machines.FractionAggregateProgram
import OAI.Combinatorics.MatchingCount.Complexity.TreeNumericCosts

namespace OAI

/-! # The exact factorial multiplier from the encoded paired state

Every factorial argument is bounded by the supplied code length. In a
valid code each cell block has length twice its capacity, so the computed
denominator is exactly the manuscript's capacity factorial.
-/

namespace ContingencyTables.PairedFactorialProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial PairedProfileProgram
open scoped BigOperators Classical

def sideFactor (z : List ℕ × Bool) : ℕ := (sideCount z).factorial
def sideFactorRealizer : Realizer sideFactor := composition sideCountRealizer factorial
lemma polynomial_sideFactor : PolynomialTime sideFactorRealizer := by
  apply polynomial_boundedFactorial polynomial_sideCount X
  intro z
  simpa only [eval_X] using (sideCount_le z.1 z.2).trans
    ((list_length_le_weight z.1).trans (weight_fst z))

def pairCount (xs : List ℕ) : ℕ := xs.length/2
def pairCountRealizer : Realizer pairCount :=
  composition (pair listLength (constant 2)) quotient
lemma polynomial_pairCount : PolynomialTime pairCountRealizer :=
  polynomial_composition (polynomial_pair polynomial_listLength (polynomial_constant 2))
    polynomial_quotient

def denominator (xs : List ℕ) : ℕ := (pairCount xs).factorial
def denominatorRealizer : Realizer denominator := composition pairCountRealizer factorial
lemma polynomial_denominator : PolynomialTime denominatorRealizer := by
  apply polynomial_boundedFactorial polynomial_pairCount X
  intro xs
  simpa only [eval_X,pairCount] using (Nat.div_le_self xs.length 2).trans (list_length_le_weight xs)

def numerator (xs : List ℕ) : ℕ := sideFactor (xs,false)*sideFactor (xs,true)
def numeratorRealizer : Realizer numerator :=
  composition (f := fun xs : List ℕ => (sideFactor (xs,false),sideFactor (xs,true)))
    (g := fun p : ℕ × ℕ => p.1*p.2)
    (pair
      (composition (f := fun xs : List ℕ => (xs,false)) (g := sideFactor)
        (pair identity (constant false)) sideFactorRealizer)
      (composition (f := fun xs : List ℕ => (xs,true)) (g := sideFactor)
        (pair identity (constant true)) sideFactorRealizer)) multiply
lemma polynomial_numerator : PolynomialTime numeratorRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant false))
      polynomial_sideFactor)
    (polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant true))
      polynomial_sideFactor)) polynomial_multiply

def rowRatio (xs : List ℕ) : TreeFraction.Fraction :=
  TreeFraction.normalize (numerator xs,denominator xs)
def rowRatioRealizer : Realizer rowRatio :=
  composition (pair numeratorRealizer denominatorRealizer) TreeFraction.normalizeRealizer
lemma polynomial_rowRatio : PolynomialTime rowRatioRealizer :=
  polynomial_composition (polynomial_pair polynomial_numerator polynomial_denominator)
    TreeFraction.polynomial_normalize

def output (z : PairedProfileProgram.Input) : TreeFraction.Fraction :=
  FractionAggregateProgram.product ((rows z).map rowRatio)
def outputRealizer : Realizer output :=
  composition (composition rowsRealizer (map rowRatioRealizer))
    FractionAggregateProgram.productRealizer
theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition (polynomial_composition polynomial_rows
    (polynomial_map polynomial_rowRatio)) FractionAggregateProgram.polynomial_product

lemma rowRatio_value (xs : List ℕ) :
    TreeFraction.val (rowRatio xs)=
      ((sideCount (xs,false)).factorial:ℚ)*(sideCount (xs,true)).factorial /
        (xs.length/2).factorial := by
  rw [rowRatio,TreeFraction.normalize_val]
  simp only [TreeFraction.val,numerator,sideFactor,denominator,pairCount,Nat.cast_mul]

noncomputable section
open PairedProfileSemantics InitialTransversals CanonicalInitialEncoding
open CompanionArithmeticProposal CompanionFactorialApplication

variable {q : ℕ} (b : Fin q → ℕ)

theorem output_canonical (S : Set (Copy b × Bool)) :
    TreeFraction.val (output (List.ofFn b,encodeSet (coordinateEquiv b) S))=
      ∏ i : Fin q,
        ((∑ k : Fin (b i), if ((⟨i,k⟩ : Copy b),false) ∈ S then 1 else 0).factorial:ℚ)*
          (∑ k : Fin (b i), if ((⟨i,k⟩ : Copy b),true) ∈ S then 1 else 0).factorial /
            (b i).factorial := by
  rw [output,FractionAggregateProgram.product_value,rows_encode]
  simp only [cellRows,List.map_ofFn,List.prod_ofFn,Function.comp_apply]
  apply Finset.prod_congr rfl
  intro i _
  rw [rowRatio_value]
  have hc := counts_cellRow b S i
  have hfalse := congrArg Prod.fst hc
  have htrue := congrArg Prod.snd hc
  change sideCount (_,false)=_ at hfalse
  change sideCount (_,true)=_ at htrue
  rw [hfalse,htrue,interleave_length,List.length_ofFn,
    Nat.mul_div_cancel_left _ (by decide : 0 < 2)]

variable {m n : ℕ} (A : Instance (Fin m) (Fin n))

/-- The multiplier used by the executed weight oracle is the literal
factorial ratio, for every subset, not just transversal states. -/
theorem output_physical (S : Set (Labels A × Bool)) :
    TreeFraction.val (output (List.ofFn (CompanionComputedInitial.capacities A),
      encodeSet (CompanionComputedInitial.coordinateOrder A) S))=
        CompanionWeightOracle.factorialRatio A S := by
  rw [CompanionComputedInitial.encodeSet_reindex,output_canonical]
  have hp (i) (side : Bool) :=
    (physical_profile_reindex A S ((CompanionComputedInitial.cellOrder A).symm i) side).trans
      (by rw [Equiv.apply_symm_apply,copy_viewCount])
  simp_rw [←hp]
  symm
  unfold CompanionWeightOracle.factorialRatio CompanionWeightOracle.factorialNumerator
    CompanionWeightOracle.factorialDenominator
  simp only [Nat.cast_prod,Fintype.prod_prod_type,Fintype.prod_bool,Nat.cast_mul]
  rw [←Finset.prod_div_distrib]
  exact Fintype.prod_equiv (CompanionComputedInitial.cellOrder A) _ _ (fun s => by
    simp only [Equiv.symm_apply_apply,CompanionComputedInitial.capacities]
    ring)

end
end ContingencyTables.PairedFactorialProgram

end OAI
