import OAI.Combinatorics.ContingencyTables.Rooted.RootedCorrectionSampleProgram
import OAI.Combinatorics.ContingencyTables.Rooted.RootedRatioSampleProgram
import OAI.Combinatorics.ContingencyTables.Machines.FractionAggregateProgram

namespace OAI

/-! # Executed sample blocks and the product weight estimator

The lists contain the actual sample inputs and their disjoint finite
words. Each sample is evaluated by the checked binary program before
its average or product is formed.
-/

namespace ContingencyTables.RootedEstimatorBlockProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped

abbrev RatioBlock := List RootedRatioSampleProgram.SampleInput
abbrev CorrectionBlock := List RootedCorrectionSampleProgram.Input

def ratioAverage (xs : RatioBlock) : TreeFraction.Fraction :=
  FractionAggregateProgram.average (xs.map RootedRatioSampleProgram.output)
def ratioAverageRealizer : Realizer ratioAverage :=
  composition (f := fun xs : RatioBlock => xs.map RootedRatioSampleProgram.output)
    (g := FractionAggregateProgram.average) (map RootedRatioSampleProgram.outputRealizer)
    FractionAggregateProgram.averageRealizer
lemma polynomial_ratioAverage : PolynomialTime ratioAverageRealizer :=
  polynomial_composition (polynomial_map RootedRatioSampleProgram.polynomial_output)
    FractionAggregateProgram.polynomial_average

def correctionAverage (xs : CorrectionBlock) : TreeFraction.Fraction :=
  FractionAggregateProgram.average (xs.map RootedCorrectionSampleProgram.output)
def correctionAverageRealizer : Realizer correctionAverage :=
  composition (f := fun xs : CorrectionBlock => xs.map RootedCorrectionSampleProgram.output)
    (g := FractionAggregateProgram.average) (map RootedCorrectionSampleProgram.outputRealizer)
    FractionAggregateProgram.averageRealizer
lemma polynomial_correctionAverage : PolynomialTime correctionAverageRealizer :=
  polynomial_composition (polynomial_map RootedCorrectionSampleProgram.polynomial_output)
    FractionAggregateProgram.polynomial_average

abbrev Input := (ℕ × List RatioBlock) × CorrectionBlock

attribute [local irreducible] ratioAverage correctionAverage

def ratioProduct (z : Input) : TreeFraction.Fraction :=
  FractionAggregateProgram.product (z.1.2.map ratioAverage)
def ratioProductRealizer : Realizer ratioProduct :=
  composition (f := fun z : Input => z.1.2.map ratioAverage)
    (g := FractionAggregateProgram.product)
    (composition (f := fun z : Input => z.1.2) (g := fun xs : List RatioBlock => xs.map ratioAverage)
      (composition first second) (map ratioAverageRealizer)) FractionAggregateProgram.productRealizer
lemma polynomial_ratioProduct : PolynomialTime ratioProductRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_composition polynomial_first polynomial_second)
    (polynomial_map polynomial_ratioAverage)) FractionAggregateProgram.polynomial_product

def factors (z : Input) : TreeFraction.Fraction :=
  TreeFraction.mul (ratioProduct z,correctionAverage z.2)
def factorsRealizer : Realizer factors :=
  composition (f := fun z : Input => (ratioProduct z,correctionAverage z.2)) (g := TreeFraction.mul)
    (pair ratioProductRealizer (composition (f := fun z : Input => z.2)
      (g := correctionAverage) second correctionAverageRealizer)) TreeFraction.mulRealizer
lemma polynomial_factors : PolynomialTime factorsRealizer :=
  polynomial_composition (polynomial_pair polynomial_ratioProduct
    (polynomial_composition polynomial_second polynomial_correctionAverage)) TreeFraction.polynomial_mul

def output (z : Input) : TreeFraction.Fraction := TreeFraction.mul ((z.1.1,1),factors z)
def outputRealizer : Realizer output :=
  composition (f := fun z : Input => ((z.1.1,1),factors z)) (g := TreeFraction.mul)
    (pair (pair (composition first first) (constant 1)) factorsRealizer) TreeFraction.mulRealizer
theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_pair (polynomial_composition polynomial_first polynomial_first) (polynomial_constant 1))
    polynomial_factors) TreeFraction.polynomial_mul

lemma ratioAverage_value (xs : RatioBlock) :
    TreeFraction.val (ratioAverage xs)=
      (xs.map (fun z => TreeFraction.val (RootedRatioSampleProgram.output z))).sum/(xs.length:ℚ) := by
  rw [ratioAverage,FractionAggregateProgram.average_value]
  simp only [List.map_map,Function.comp_def,List.length_map]

lemma correctionAverage_value (xs : CorrectionBlock) :
    TreeFraction.val (correctionAverage xs)=
      (xs.map (fun z => TreeFraction.val (RootedCorrectionSampleProgram.output z))).sum/(xs.length:ℚ) := by
  rw [correctionAverage,FractionAggregateProgram.average_value]
  simp only [List.map_map,Function.comp_def,List.length_map]

lemma output_value (z : Input) :
    TreeFraction.val (output z)=(z.1.1:ℚ)*
      (z.1.2.map (fun xs => TreeFraction.val (ratioAverage xs))).prod*
        TreeFraction.val (correctionAverage z.2) := by
  rw [output,TreeFraction.mul_val,factors,TreeFraction.mul_val,ratioProduct,
    FractionAggregateProgram.product_value]
  rw [show TreeFraction.val (z.1.1,1)=(z.1.1:ℚ) by
    simp only [TreeFraction.val,Nat.cast_one,div_one]]
  simp only [List.map_map,Function.comp_def]
  ring

end ContingencyTables.RootedEstimatorBlockProgram

end OAI
