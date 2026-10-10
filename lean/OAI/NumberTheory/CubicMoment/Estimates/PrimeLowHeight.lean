import OAI.NumberTheory.CubicMoment.Estimates.PrimeHeightDecomposition
import OAI.NumberTheory.CubicMoment.Estimates.LowHeightIntegral

namespace OAI

/-! Transfer a uniform low-height arithmetic bound to the actual
low-height term of the sharp prime comparison. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma lowHeightWeight_integrable {H : ℝ} (hH : 0 < H) (T : ℝ) :
    Integrable (lowHeightWeight H T) := by
  apply (cutoffHeightMultiplier_integrable hH).mul_bdd (c := 1)
  · exact (Complex.continuous_ofReal.comp
      (heightPartitionBump.continuous.comp (continuous_id.div_const T))).aestronglyMeasurable
  · filter_upwards with t
    simpa only [Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg heightPartitionBump.nonneg] using
      (heightPartitionBump.le_one (x := t/T))

theorem finiteHeightLow_bound (P : Finset Eisenstein) (c : Eisenstein → ℂ)
    {H T B : ℝ} (hH : 0 < H) (hT : 0 < T) (hB : 0 ≤ B) (X₀ : ℝ)
    (hf : ∀ t ∈ Set.Icc (-(4/3)*T) ((4/3)*T),
      ‖∑ p ∈ P, c p*normTwist t p‖ ≤ B) :
    ‖finiteHeightLow P c H T X₀‖ ≤ (8/3)*Real.log 2*T*B := by
  have he := height_norm_polynomial_integral P c id (lowHeightWeight H T)
    (lowHeightWeight_integrable hH T) (Real.log X₀)
  simp only [id_eq] at he
  change ‖∑ p ∈ P, c p*heightFourierIntegral (lowHeightWeight H T)
    (Real.log (norm p)-Real.log X₀)‖ ≤ _
  rw [he]
  have hb := lowHeightWeight_integral_bound H hT hB
    (fun t => Complex.exp ((-Real.log X₀*t:ℝ)*Complex.I)*∑ p ∈ P, c p*normTwist t p)
    (by
      intro t ht
      rw [norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]
      exact hf t ht)
  simpa only [mul_assoc] using hb

theorem primeComparisonLowHeight_bound (ℓ : ℤ) {H T X B : ℝ}
    (hH : 0 < H) (hT : 0 < T) (hB : 0 ≤ B)
    (hf : ∀ t ∈ Set.Icc (-(4/3)*T) ((4/3)*T),
      ‖∑ p ∈ primeCutoff (4*X), primeComparisonCoefficient ℓ p*normTwist t p‖ ≤ B) :
    ‖primeComparisonLowHeight ℓ H T X‖ ≤ (8/3)*Real.log 2*T*B :=
  finiteHeightLow_bound _ _ hH hT hB X hf

end CubicFirstMoment

end

end OAI
