import OAI.NumberTheory.CubicMoment.Estimates.SquarefreeTwists
import OAI.NumberTheory.CubicMoment.Estimates.StructuredMeanValue

namespace OAI

/-! Exact collection of angular coordinate tuples. The same fixed theta
factor occurs on each original coordinate and hence on their product. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def primaryAngularCoefficientTuple (ℓ : ℤ) (A : Eisenstein → ℂ)
    (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑ n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y)),
    (∏ i, A (n i)*W i (norm (n i)/X i)*
      (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*
        theta ℓ (n i)*mellinPhase (t i) (norm (n i))))*V ((∏ i, norm (n i))/Y)

def primaryAngularPrimeIndicatorTuple (ℓ : ℤ) (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  primaryAngularCoefficientTuple ℓ (fun n => (primeIndicator n:ℂ)) a b q η t W X V Y

lemma angular_coordinate_convolution_collection (ℓ : ℤ) (A : Eisenstein → ℂ)
    (a b : Eisenstein) (ha : primary a) (hb : primary b)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) :
    primaryAngularCoefficientTuple ℓ A a b q η t W X V Y =
      ∑ z ∈ orderedConvolutionSupport (coordinateSupport W X Y),
        orderedConvolution (coordinateSupport W X Y)
          (fun i n => A n*coordinateFactor q η t W X i n) z*
            (mixedCubic a b z*theta ℓ z*V (norm z/Y)) := by
  let χ : Eisenstein →* ℂ :=
    { toFun := theta ℓ, map_one' := theta_one ℓ, map_mul' := theta_mul ℓ }
  have he : primaryAngularCoefficientTuple ℓ A a b q η t W X V Y =
      ∑ n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y)),
        (∏ i, (A (n i)*χ (n i))*W i (norm (n i)/X i)*
          (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*
            mellinPhase (t i) (norm (n i))))*V ((∏ i, norm (n i))/Y) := by
    unfold primaryAngularCoefficientTuple
    apply Finset.sum_congr rfl
    intro n _
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    simp only [χ, MonoidHom.coe_mk, OneHom.coe_mk]
    ring
  rw [he,coordinate_convolution_collection (fun n => A n*χ n) a b ha hb q η t W X V Y]
  apply Finset.sum_congr rfl
  intro z _
  have hw : (fun i n => (A n*χ n)*coordinateFactor q η t W X i n) =
      (fun i n => (A n*coordinateFactor q η t W X i n)*χ n) := by
    funext i n
    ring
  rw [hw,orderedConvolution_mul_character]
  change (_*theta ℓ z)*_ = _
  ring

def angularPrimeCoordinateError (ℓ : ℤ) (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑ z ∈ coordinateProductCutoff W X Y,
    primeLogConvolutionError (coordinateSupport W X Y) (coordinateFactor q η t W X) z*
      (mixedCubic a b z*theta ℓ z*V (norm z/Y))

lemma angular_normalized_prime_tuple_difference (ℓ : ℤ) (a b : Eisenstein)
    (ha : primary a) (hb : primary b) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y)
    (hV : ∀ x, 2 < x → V x = 0) :
    primaryAngularCoefficientTuple ℓ (fun n => (normalizedVonMangoldt n:ℂ)) a b q η t W X V Y-
      primaryAngularPrimeIndicatorTuple ℓ a b q η t W X V Y =
        angularPrimeCoordinateError ℓ a b q η t W X V Y := by
  rw [primaryAngularPrimeIndicatorTuple,
    angular_coordinate_convolution_collection ℓ _ a b ha hb,
    angular_coordinate_convolution_collection ℓ _ a b ha hb,← Finset.sum_sub_distrib]
  have he : (∑ z ∈ orderedConvolutionSupport (coordinateSupport W X Y),
      (orderedConvolution (coordinateSupport W X Y)
        (fun i n => (normalizedVonMangoldt n:ℂ)*coordinateFactor q η t W X i n) z*
          (mixedCubic a b z*theta ℓ z*V (norm z/Y))-
       orderedConvolution (coordinateSupport W X Y)
        (fun i n => (primeIndicator n:ℂ)*coordinateFactor q η t W X i n) z*
          (mixedCubic a b z*theta ℓ z*V (norm z/Y)))) =
      ∑ z ∈ orderedConvolutionSupport (coordinateSupport W X Y),
        primeLogConvolutionError (coordinateSupport W X Y) (coordinateFactor q η t W X) z*
          (mixedCubic a b z*theta ℓ z*V (norm z/Y)) := by
    apply Finset.sum_congr rfl
    intro z _
    unfold primeLogConvolutionError
    ring
  rw [he]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro z hz hnot
  have hlarge : 2*Y < norm z := lt_of_not_ge (fun h => hnot (Finset.mem_filter.mpr ⟨hz,h⟩))
  have hv := hV (norm z/Y) ((lt_div_iff₀ hY).mpr hlarge)
  simp only [hv,mul_zero]

lemma angular_primeIndicatorTuple_eq_prime_convolution (ℓ : ℤ) (a b : Eisenstein)
    (ha : primary a) (hb : primary b) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) :
    primaryAngularPrimeIndicatorTuple ℓ a b q η t W X V Y =
      ∑ z ∈ orderedConvolutionSupport (coordinatePrimeSupport W X Y),
        orderedConvolution (coordinatePrimeSupport W X Y) (coordinateFactor q η t W X) z*
          (mixedCubic a b z*theta ℓ z*V (norm z/Y)) := by
  rw [primaryAngularPrimeIndicatorTuple,angular_coordinate_convolution_collection ℓ _ a b ha hb]
  simp_rw [orderedConvolution_primeIndicator]
  symm
  apply Finset.sum_subset
  · intro z hz
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image.mpr ⟨n,Fintype.mem_piFinset.mpr (fun i =>
      (Finset.mem_filter.mp (Fintype.mem_piFinset.mp hn i)).1),rfl⟩
  · intro z _ hnot
    rw [orderedConvolution_eq_zero_of_not_mem _ _ hnot,zero_mul]

def primaryAngularSquarefreePrimeTuple (ℓ : ℤ) (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑ z ∈ orderedConvolutionSupport (coordinatePrimeSupport W X Y),
    squarefreeConvolution (coordinatePrimeSupport W X Y) (coordinateFactor q η t W X) z*
      (mixedCubic a b z*theta ℓ z*V (norm z/Y))

def angularSquarefreeCoordinateError (ℓ : ℤ) (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑ z ∈ coordinatePrimeCutoff W X Y,
    squarefreeConvolutionError (coordinatePrimeSupport W X Y) (coordinateFactor q η t W X) z*
      (mixedCubic a b z*theta ℓ z*V (norm z/Y))

lemma angular_primeIndicator_sub_squarefree_cutoff (ℓ : ℤ) (a b : Eisenstein)
    (ha : primary a) (hb : primary b) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y)
    (hV : ∀ x, 2 < x → V x = 0) :
    primaryAngularPrimeIndicatorTuple ℓ a b q η t W X V Y-
      primaryAngularSquarefreePrimeTuple ℓ a b q η t W X V Y =
        angularSquarefreeCoordinateError ℓ a b q η t W X V Y := by
  rw [angular_primeIndicatorTuple_eq_prime_convolution ℓ a b ha hb]
  unfold primaryAngularSquarefreePrimeTuple angularSquarefreeCoordinateError
  rw [← Finset.sum_sub_distrib]
  simp only [squarefreeConvolutionError,sub_mul]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro z hz hnot
  have hlarge : 2*Y < norm z := lt_of_not_ge (fun h => hnot (Finset.mem_filter.mpr ⟨hz,h⟩))
  have hv := hV (norm z/Y) ((lt_div_iff₀ hY).mpr hlarge)
  simp only [hv,mul_zero,sub_self]

end CubicFirstMoment

end

end OAI
