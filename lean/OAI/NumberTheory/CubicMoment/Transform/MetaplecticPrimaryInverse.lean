import OAI.NumberTheory.CubicMoment.Transform.MetaplecticPrimaryCompletion
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticPrimalFinite

namespace OAI

/-! The exact inverse completion at primary elements. The formal Euler
inverse is reindexed onto the literal primary cube-divisor fibers, with
its actual Möbius, angular and height weights. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticPrimeCompletionWeights (r : Eisenstein) (ℓ : ℤ) (t : ℝ)
    (p : EisensteinIdealPrime) : ℂ :=
  metaplecticCompletionWeight r ℓ t (primaryNormalize (idealPrimeRepresentative p))

lemma weightedInverseCompletion_eq (r : Eisenstein) (ℓ : ℤ) (t : ℝ) :
    weightedCubeSeries (MvPowerSeries.map Complex.ofRealHom idealMoebiusSeries)
      (metaplecticPrimeCompletionWeights r ℓ t) =
        cubeInverseCompletionSeries (metaplecticPrimeCompletionWeights r ℓ t) := rfl

/-- No cube-divisor is omitted: the finite bound follows from divisibility
of the original primary element, not from an additional support hypothesis. -/
theorem metaplectic_primary_inverse_coefficient
    (r : Eisenstein) (ℓ : ℤ) (t : ℝ) (A : ComplexIdealSeries)
    {b : Eisenstein} (hb : primary b) {F : ℝ} (hbF : norm b ≤ F) :
    MvPowerSeries.coeff (idealExponentOf b) A =
      ∑ n ∈ primaryCubeFiber F b,
        ((idealMoebius (n 0):ℂ)*metaplecticCompletionWeight r ℓ t (n 0))*
          MvPowerSeries.coeff (idealExponentOf (n 1))
            (cubeCompletionSeries (metaplecticPrimeCompletionWeights r ℓ t)*A) := by
  have he := weightedCubeSeries_product_primary
    (MvPowerSeries.map Complex.ofRealHom idealMoebiusSeries)
    (cubeCompletionSeries (metaplecticPrimeCompletionWeights r ℓ t)*A)
    (metaplecticPrimeCompletionWeights r ℓ t) hb hbF
  rw [weightedInverseCompletion_eq,cube_completion_inversion] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro n hn
  have hc := (mem_primaryElementBall.mp
    (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hn).1 0)).1
  simp only [metaplecticPrimeCompletionWeights]
  rw [MvPowerSeries.coeff_map,
    idealMoebiusSeries_at_element (primary_ne_zero hc),
    normalized_prime_product_character hc le_rfl
      (metaplecticCompletionWeight r ℓ t) (metaplecticCompletionWeight_one r ℓ t)
      (fun _ _ ha hb => metaplecticCompletionWeight_mul r ℓ t ha hb),
    idealPrimaryGenerator_at_element hc]
  simp only [Complex.ofRealHom_eq_coe]
  push_cast
  ring

/-- Any finite smooth norm weight may be applied after the actual primary
inverse identity, without a rearrangement of an infinite series. -/
theorem metaplectic_primary_weighted_inverse
    (r : Eisenstein) (ℓ : ℤ) (t : ℝ) (A : ComplexIdealSeries)
    (F : ℝ) (W : ℝ → ℂ) :
    (∑ b ∈ primaryElementBall F, W (norm b)*MvPowerSeries.coeff (idealExponentOf b) A) =
      ∑ b ∈ primaryElementBall F, W (norm b)*
        ∑ n ∈ primaryCubeFiber F b,
          ((idealMoebius (n 0):ℂ)*metaplecticCompletionWeight r ℓ t (n 0))*
            MvPowerSeries.coeff (idealExponentOf (n 1))
              (cubeCompletionSeries (metaplecticPrimeCompletionWeights r ℓ t)*A) := by
  apply Finset.sum_congr rfl
  intro b hb
  rw [metaplectic_primary_inverse_coefficient r ℓ t A
    (mem_primaryElementBall.mp hb).1 (mem_primaryElementBall.mp hb).2]

def metaplecticGaussIdealSeries (r : Eisenstein) (ℓ : ℤ) (t : ℝ) :
    ComplexIdealSeries := fun ν =>
      gauss (r*idealPrimaryGenerator ν)*theta ℓ (r*idealPrimaryGenerator ν)*
        mellinPhase t (idealExponentNorm ν)

lemma metaplecticGaussIdealSeries_at_primary (r : Eisenstein) (ℓ : ℤ) (t : ℝ)
    {b : Eisenstein} (hb : primary b) :
    MvPowerSeries.coeff (idealExponentOf b) (metaplecticGaussIdealSeries r ℓ t) =
      gauss (r*b)*theta ℓ (r*b)*mellinPhase t (norm b) := by
  simp only [MvPowerSeries.coeff_apply,metaplecticGaussIdealSeries,
    idealPrimaryGenerator_at_element hb,idealExponentOf_norm (primary_ne_zero hb)]

/-- The inverted coefficients are the literal angular Gauss coefficients,
including the original norm twist. -/
theorem metaplectic_gauss_primary_inverse
    (r : Eisenstein) (ℓ : ℤ) (t F : ℝ) (W : ℝ → ℂ) :
    (∑ b ∈ primaryElementBall F, W (norm b)*
      (gauss (r*b)*theta ℓ (r*b)*mellinPhase t (norm b))) =
      ∑ b ∈ primaryElementBall F, W (norm b)*
        ∑ n ∈ primaryCubeFiber F b,
          ((idealMoebius (n 0):ℂ)*metaplecticCompletionWeight r ℓ t (n 0))*
            MvPowerSeries.coeff (idealExponentOf (n 1))
              (cubeCompletionSeries (metaplecticPrimeCompletionWeights r ℓ t)*
                metaplecticGaussIdealSeries r ℓ t) := by
  rw [←metaplectic_primary_weighted_inverse]
  apply Finset.sum_congr rfl
  intro b hb
  rw [metaplecticGaussIdealSeries_at_primary r ℓ t (mem_primaryElementBall.mp hb).1]

end CubicFirstMoment

end

end OAI
