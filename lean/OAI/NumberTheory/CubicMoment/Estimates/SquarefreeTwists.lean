import OAI.NumberTheory.CubicMoment.Estimates.PrimeIndicatorCollection
import OAI.NumberTheory.CubicMoment.Estimates.ResidueProducts
import OAI.NumberTheory.CubicMoment.Estimates.PrimaryConvolutionEnergy

namespace OAI

/-! Exact multiplicative twists of the manuscript's squarefree prime coefficient. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma orderedConvolution_mul_character (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (χ : Eisenstein →* ℂ) (z : Eisenstein) :
    orderedConvolution S (fun i n => w i n*χ n) z = orderedConvolution S w z*χ z := by
  unfold orderedConvolution
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.prod_mul_distrib,← map_prod, (Finset.mem_filter.mp hn).2]

lemma squarefreeConvolution_mul_character (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (χ : Eisenstein →* ℂ) (z : Eisenstein) :
    squarefreeConvolution S (fun i n => w i n*χ n) z = squarefreeConvolution S w z*χ z := by
  by_cases hs : Squarefree z
  · simp only [squarefreeConvolution,ite_eq_left hs,orderedConvolution_mul_character]
  · simp only [squarefreeConvolution,ite_eq_right hs,zero_mul]

omit [Fintype ι] [DecidableEq ι] in
lemma coordinateFactor_product_character (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (r : Eisenstein) (ψ : MulChar (Residues r) ℂ)
    (i : ι) (n : Eisenstein) :
    coordinateFactor (fun i => q i*r) (fun i => productResidueChar (η i) ψ) t W X i n =
      coordinateFactor q η t W X i n*ψ (Ideal.Quotient.mk (modulus r) n) := by
  simp only [coordinateFactor,productResidueChar_mk]
  ring

lemma squarefreePrimeTuple_product_character (a b : Eisenstein)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ)
    (r : Eisenstein) (ψ : MulChar (Residues r) ℂ) :
    primarySquarefreePrimeTuple a b (fun i => q i*r)
      (fun i => productResidueChar (η i) ψ) t W X V Y =
      ∑ z ∈ orderedConvolutionSupport (coordinatePrimeSupport W X Y),
        squarefreeConvolution (coordinatePrimeSupport W X Y) (coordinateFactor q η t W X) z*
          (mixedCubic a b z*ψ (Ideal.Quotient.mk (modulus r) z)*V (norm z/Y)) := by
  unfold primarySquarefreePrimeTuple
  apply Finset.sum_congr rfl
  intro z hz
  have hf : coordinateFactor (fun i => q i*r)
      (fun i => productResidueChar (η i) ψ) t W X =
      fun i n => coordinateFactor q η t W X i n*ψ (Ideal.Quotient.mk (modulus r) n) := by
    funext i n
    exact coordinateFactor_product_character q η t W X r ψ i n
  rw [hf]
  let χ : Eisenstein →* ℂ := ψ.toMonoidHom.comp (Ideal.Quotient.mk (modulus r)).toMonoidHom
  change squarefreeConvolution _ (fun i n => coordinateFactor q η t W X i n*χ n) z*_
    = _
  rw [squarefreeConvolution_mul_character]
  change (_*ψ (Ideal.Quotient.mk (modulus r) z))*_ = _
  ring

lemma squarefreePrimeTuple_small_second_conductor (a b : Eisenstein) (hb : primary b)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) :
    primarySquarefreePrimeTuple a 1 (fun i => q i*(3*(1*b)))
      (fun i => productResidueChar (η i) (primaryMixedResidueChar 1 b primary_one hb))
        t W X V Y = primarySquarefreePrimeTuple a b q η t W X V Y := by
  rw [squarefreePrimeTuple_product_character]
  unfold primarySquarefreePrimeTuple
  apply Finset.sum_congr rfl
  intro z hz
  have hzprim := orderedPrimarySupport_primary (coordinatePrimeSupport W X Y)
    (fun i p hp => (coordinatePrimeSupport_primary W X Y i p hp).1) hz
  rw [primaryMixedResidueChar_primary primary_one hb hzprim]
  simp only [mixedCubic,cubicSymbol_one_lower,star_one,mul_one,one_mul]

end CubicFirstMoment

end

end OAI
