import OAI.NumberTheory.CubicMoment.Estimates.IntervalTransform
import OAI.NumberTheory.CubicMoment.Estimates.DispersionAlgebra

namespace OAI

/-!
# The actual truncated Mellin integral

The Fourier approximation to the dyadic indicator is inserted into a
finite arithmetic polynomial. The height is `2πξ`, in accordance with
Mathlib's Fourier convention. The multiplier vanishes for `|ξ| ≥ T`.
-/

noncomputable section
open MeasureTheory FourierTransform
open scoped BigOperators FourierTransform
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

def dyadicFourierMultiplier (ξ : ℝ) : ℂ :=
  𝓕 (fun x => (intervalStep 0 (Real.log 2) x : ℂ)) ξ

def truncatedMellinWeight (X T ξ : ℝ) : ℂ :=
  Complex.exp ((-2*Real.pi*ξ*Real.log X : ℝ)*Complex.I) *
    (frequencyCutoff (ξ/T) * dyadicFourierMultiplier ξ)

lemma continuous_dyadicFourierMultiplier : Continuous dyadicFourierMultiplier :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by fun_prop) (integrable_intervalStep 0 (Real.log 2))

lemma continuous_truncatedMellinWeight (X T : ℝ) : Continuous (truncatedMellinWeight X T) := by
  unfold truncatedMellinWeight
  exact (Complex.continuous_exp.comp (by fun_prop)).mul
    ((frequencyCutoff.continuous.comp (by fun_prop)).mul continuous_dyadicFourierMultiplier)

lemma truncatedMellinWeight_zero (X : ℝ) {T ξ : ℝ} (hT : 0 < T) (hξ : T ≤ |ξ|) :
    truncatedMellinWeight X T ξ = 0 := by
  unfold truncatedMellinWeight
  have hf : frequencyCutoff (ξ/T) = 0 := frequencyCutoff_zero (by
    rw [abs_div,abs_of_pos hT]
    exact (le_div_iff₀ hT).mpr (by simpa using hξ))
  rw [hf,zero_mul,mul_zero]

lemma truncatedMellinWeight_compact (X : ℝ) {T : ℝ} (hT : 0 < T) :
    HasCompactSupport (truncatedMellinWeight X T) := by
  apply HasCompactSupport.intro' (K := Set.Icc (-T) T) isCompact_Icc isClosed_Icc
  intro ξ hξ
  apply truncatedMellinWeight_zero X hT
  simp only [Set.mem_Icc,not_and_or,not_le] at hξ
  rcases hξ with hξ | hξ
  · linarith [neg_abs_le ξ]
  · exact hξ.le.trans (le_abs_self ξ)

lemma integrable_truncatedMellinWeight_twist (X : ℝ) {T : ℝ} (hT : 0 < T)
    (n : Eisenstein) :
    Integrable (fun ξ => truncatedMellinWeight X T ξ * normTwist (2*Real.pi*ξ) n) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (continuous_truncatedMellinWeight X T).mul (by unfold normTwist; fun_prop)
  · exact (truncatedMellinWeight_compact X hT).mul_right

lemma smoothLogInterval_eq_mellin {X T : ℝ} (hX : 0 < X) (hT : 0 < T)
    (n : Eisenstein) (hn : n ≠ 0) :
    smoothLogInterval T (norm n/X) =
      ∫ ξ : ℝ, truncatedMellinWeight X T ξ * normTwist (2*Real.pi*ξ) n := by
  rw [smoothLogInterval, concrete_interval_fourier_integral hT]
  apply integral_congr_ae
  filter_upwards [] with ξ
  have hn0 : norm n ≠ 0 := norm_eq_zero_iff.not.mpr hn
  rw [Real.log_div hn0 hX.ne']
  unfold truncatedMellinWeight normTwist dyadicFourierMultiplier
  have he : ((2*Real.pi*ξ*(Real.log (norm n)-Real.log X) : ℝ) : ℂ)*Complex.I =
      ((-2*Real.pi*ξ*Real.log X : ℝ) : ℂ)*Complex.I +
        (((2*Real.pi*ξ)*Real.log (norm n) : ℝ) : ℂ)*Complex.I := by
    push_cast
    ring
  rw [he,Complex.exp_add]
  ring

/-- An exact integral representation, using the same cutoff for every
coefficient. Hence the height shifts are common across character rows. -/
theorem smoothed_polynomial_eq_mellin (N : Finset Eisenstein) (v : Eisenstein → ℂ)
    {X T : ℝ} (hX : 0 < X) (hT : 0 < T) (hN : ∀ n ∈ N, n ≠ 0) :
    (∑ n ∈ N, v n * smoothLogInterval T (norm n/X)) =
      ∫ ξ : ℝ, truncatedMellinWeight X T ξ *
        (∑ n ∈ N, v n * normTwist (2*Real.pi*ξ) n) := by
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum N (fun n _ =>
    ((integrable_truncatedMellinWeight_twist X hT n).const_mul (v n)).congr
      (Filter.Eventually.of_forall (fun ξ => by ring)))]
  apply Finset.sum_congr rfl
  intro n hn
  rw [smoothLogInterval_eq_mellin hX hT n (hN n hn), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with ξ
  ring

end CubicFirstMoment

end

end OAI
