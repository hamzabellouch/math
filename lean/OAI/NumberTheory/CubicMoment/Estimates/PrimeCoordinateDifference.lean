import OAI.NumberTheory.CubicMoment.Estimates.PrimeCoordinateCollection

namespace OAI

/-! The exact difference between normalized von Mangoldt tuples and
original prime-indicator tuples on the global smooth cutoff. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def primaryPrimeIndicatorTuple (a b : Eisenstein) (q : ι → Eisenstein)
    (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑ n ∈ Fintype.piFinset (fun _ : ι => primaryElementBall (2*Y)),
    (∏ i, (primeIndicator (n i):ℂ)*W i (norm (n i)/X i)*
      (mixedCubic a b (n i)*η i (Ideal.Quotient.mk (modulus (q i)) (n i))*
        mellinPhase (t i) (norm (n i))))*V ((∏ i, norm (n i))/Y)

def coordinateProductCutoff (W : ι → ℝ → ℂ) (X : ι → ℝ) (Y : ℝ) : Finset Eisenstein :=
  (orderedConvolutionSupport (coordinateSupport W X Y)).filter (fun b => norm b ≤ 2*Y)

lemma coordinateProductCutoff_spec (W : ι → ℝ → ℂ) (X : ι → ℝ) (Y : ℝ) :
    coordinateProductCutoff W X Y ⊆ orderedConvolutionSupport (coordinateSupport W X Y) ∧
      ∀ b ∈ coordinateProductCutoff W X Y, norm b ≤ 2*Y :=
  ⟨Finset.filter_subset _ _,fun _ hb => (Finset.mem_filter.mp hb).2⟩

lemma normalized_prime_tuple_difference (a b : Eisenstein) (ha : primary a) (hb : primary b)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y)
    (hV : ∀ x, 2 < x → V x = 0) :
    primaryNormalizedVonMangoldtTuple a b q η t W X V Y-
        primaryPrimeIndicatorTuple a b q η t W X V Y =
      ∑ z ∈ coordinateProductCutoff W X Y,
        primeLogConvolutionError (coordinateSupport W X Y) (coordinateFactor q η t W X) z*
          (mixedCubic a b z*V (norm z/Y)) := by
  have hn := coordinate_convolution_collection (fun n => (normalizedVonMangoldt n:ℂ))
    a b ha hb q η t W X V Y
  have hp := coordinate_convolution_collection (fun n => (primeIndicator n:ℂ))
    a b ha hb q η t W X V Y
  change primaryNormalizedVonMangoldtTuple a b q η t W X V Y = _ at hn
  change primaryPrimeIndicatorTuple a b q η t W X V Y = _ at hp
  rw [hn,hp,← Finset.sum_sub_distrib]
  have he : (∑ z ∈ orderedConvolutionSupport (coordinateSupport W X Y),
      (orderedConvolution (coordinateSupport W X Y)
        (fun i n => (normalizedVonMangoldt n:ℂ)*coordinateFactor q η t W X i n) z*
          (mixedCubic a b z*V (norm z/Y))-
       orderedConvolution (coordinateSupport W X Y)
        (fun i n => (primeIndicator n:ℂ)*coordinateFactor q η t W X i n) z*
          (mixedCubic a b z*V (norm z/Y)))) =
      ∑ z ∈ orderedConvolutionSupport (coordinateSupport W X Y),
        primeLogConvolutionError (coordinateSupport W X Y) (coordinateFactor q η t W X) z*
          (mixedCubic a b z*V (norm z/Y)) := by
    apply Finset.sum_congr rfl
    intro z hz
    unfold primeLogConvolutionError
    ring
  rw [he]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro z hz hnot
  have hlarge : 2*Y < norm z := lt_of_not_ge (fun h => hnot (Finset.mem_filter.mpr ⟨hz,h⟩))
  have hv := hV (norm z/Y) ((lt_div_iff₀ hY).mpr hlarge)
  rw [hv,mul_zero,mul_zero]

end CubicFirstMoment

end

end OAI
