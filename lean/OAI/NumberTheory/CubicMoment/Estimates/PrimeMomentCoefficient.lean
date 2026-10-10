import OAI.NumberTheory.CubicMoment.Estimates.SquarefreeTwists
import OAI.NumberTheory.CubicMoment.Estimates.CubicNumeratorCharacter

namespace OAI

/-! Exact identification of the structured moment with the original
squarefree ordered-prime coefficient, including numerator and exclusion. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma mellinPhase_norm_prod {α : Type*} (S : Finset α) (f : α → Eisenstein)
    (u : ℝ) (hf : ∀ i ∈ S, f i ≠ 0) :
    mellinPhase u (norm (∏ i ∈ S, f i)) = ∏ i ∈ S, mellinPhase u (norm (f i)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [mellinPhase,norm]
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi,Finset.prod_insert hi,← normTwist_eq_mellinPhase,
      normTwist_mul u (hf i (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => hf j (Finset.mem_insert_of_mem hj))),
      normTwist_eq_mellinPhase,normTwist_eq_mellinPhase,
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

lemma orderedConvolution_norm_twist (S : ι → Finset Eisenstein)
    (hS : ∀ i, ∀ n ∈ S i, n ≠ 0) (w : ι → Eisenstein → ℂ) (u : ℝ) (z : Eisenstein) :
    orderedConvolution S (fun i n => w i n*mellinPhase u (norm n)) z =
      orderedConvolution S w z*mellinPhase u (norm z) := by
  unfold orderedConvolution
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.prod_mul_distrib,← mellinPhase_norm_prod Finset.univ n u
    (fun i _ => hS i (n i) (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hn).1 i)),
    (Finset.mem_filter.mp hn).2]

lemma squarefreeConvolution_norm_twist (S : ι → Finset Eisenstein)
    (hS : ∀ i, ∀ n ∈ S i, n ≠ 0) (w : ι → Eisenstein → ℂ) (u : ℝ) (z : Eisenstein) :
    squarefreeConvolution S (fun i n => w i n*mellinPhase u (norm n)) z =
      squarefreeConvolution S w z*mellinPhase u (norm z) := by
  by_cases hs : Squarefree z
  · simp only [squarefreeConvolution,ite_eq_left hs,orderedConvolution_norm_twist S hS]
  · simp only [squarefreeConvolution,ite_eq_right hs,zero_mul]

def primeMomentCoefficient (W : ι → ℝ → ℂ) (X : ι → ℝ) (Y : ℝ) (z : Eisenstein) : ℂ :=
  squarefreeConvolution (coordinatePrimeSupport W X Y) (fun i n => W i (norm n/X i)) z

def structuredPrimeMoment (a b v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑ z ∈ (orderedConvolutionSupport (coordinatePrimeSupport W X Y)).filter
      (fun z => IsCoprime z e),
    primeMomentCoefficient W X Y z*mellinPhase u (norm z)*
      cubicSymbol z (v*a*b^2)*V (norm z/Y)

lemma mixedCubic_numerator {a b z : Eisenstein} (ha : primary a) (hb : primary b)
    (hz : primary z) : mixedCubic a b z = cubicSymbol z (a*b^2) := by
  rw [mixedCubic,cubic_reciprocity ha hz,cubic_reciprocity hb hz,
    pow_two,cubicSymbol_mul_upper hz,cubicSymbol_mul_upper hz,← cubicSymbol_sq_eq_star hz]
  ring

lemma principal_residue_value (e z : Eisenstein) :
    (1 : MulChar (Residues e) ℂ) (Ideal.Quotient.mk (modulus e) z) =
      if IsCoprime z e then 1 else 0 := by
  by_cases hc : IsCoprime z e
  · rw [ite_eq_left hc,MulChar.one_apply (residue_isUnit_of_isCoprime hc.symm)]
  · rw [ite_eq_right hc]
    exact MulChar.map_nonunit _ (fun h => hc (isCoprime_of_residue_isUnit h).symm)

lemma squarefreePrimeTuple_principal_base (a b : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) :
    primarySquarefreePrimeTuple a b (fun _ : ι => 1) (fun _ => 1) (fun _ => u) W X V Y =
      ∑ z ∈ orderedConvolutionSupport (coordinatePrimeSupport W X Y),
        primeMomentCoefficient W X Y z*mellinPhase u (norm z)*
          (mixedCubic a b z*V (norm z/Y)) := by
  have hf : coordinateFactor (fun _ : ι => 1) (fun _ => 1) (fun _ => u) W X =
      fun i n => W i (norm n/X i)*mellinPhase u (norm n) := by
    funext i n
    simp only [coordinateFactor,MulChar.one_apply (residue_isUnit_of_isCoprime isCoprime_one_left),mul_one]
  unfold primarySquarefreePrimeTuple
  rw [hf]
  apply Finset.sum_congr rfl
  intro z hz
  rw [squarefreeConvolution_norm_twist _
    (fun i n hn => (coordinatePrimeSupport_primary W X Y i n hn).2.ne_zero)]
  rfl

/-- The literal numerator and excluded-prime factors are assembled into
one explicitly constructed finite character of modulus 9ve. -/
lemma structuredPrimeMoment_eq_tuple (hpub : CubicSupplementaryPeriodicity)
    (a b v e : Eisenstein) (ha : primary a) (hb : primary b) (hv : v ≠ 0)
    (u : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) :
    structuredPrimeMoment a b v e u W X V Y =
      primarySquarefreePrimeTuple a b (fun _ : ι => 1*((9*v)*e))
        (fun _ => productResidueChar (1 : MulChar (Residues (1:Eisenstein)) ℂ)
          (productResidueChar (cubicNumeratorChar hpub v hv) (1 : MulChar (Residues e) ℂ)))
        (fun _ => u) W X V Y := by
  rw [squarefreePrimeTuple_product_character]
  have hf : coordinateFactor (fun _ : ι => 1) (fun _ => 1) (fun _ => u) W X =
      fun i n => W i (norm n/X i)*mellinPhase u (norm n) := by
    funext i n
    simp only [coordinateFactor,MulChar.one_apply (residue_isUnit_of_isCoprime isCoprime_one_left),mul_one]
  rw [hf,structuredPrimeMoment,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  have hzprim := orderedPrimarySupport_primary (coordinatePrimeSupport W X Y)
    (fun i n hn => (coordinatePrimeSupport_primary W X Y i n hn).1) hz
  rw [squarefreeConvolution_norm_twist _
    (fun i n hn => (coordinatePrimeSupport_primary W X Y i n hn).2.ne_zero),
    productResidueChar_mk,cubicNumeratorChar_primary hpub v hv hzprim,principal_residue_value]
  by_cases hcop : IsCoprime z e
  · rw [ite_eq_left hcop,ite_eq_left hcop,mul_one,mixedCubic_numerator ha hb hzprim,
      cubicSymbol_mul_upper hzprim]
    simp only [cubicSymbol_mul_upper hzprim]
    unfold primeMomentCoefficient
    ring
  · simp only [ite_eq_right hcop,mul_zero,zero_mul]

end CubicFirstMoment

end

end OAI
