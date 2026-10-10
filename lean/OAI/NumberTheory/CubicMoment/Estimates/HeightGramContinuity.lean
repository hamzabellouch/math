import OAI.NumberTheory.CubicMoment.Estimates.HeightMeanSquare
import OAI.NumberTheory.CubicMoment.Estimates.CommonOuterLogSaving

namespace OAI

/-! Continuity of the literal variance follows from its finite Gram
identity; the unit square-divisor is exactly the unrestricted variance. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma continuous_dispersionPolynomial (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (a : Eisenstein) : Continuous (fun u => dispersionPolynomial S β u a) := by
  unfold dispersionPolynomial
  apply continuous_finsetSum
  intro b hb
  exact ((continuous_const.mul (continuous_normTwist b)).mul continuous_const).mul continuous_const

lemma continuous_dispersionAmplitude (β : Eisenstein → ℂ) (a : Eisenstein) :
    Continuous (fun u => dispersionAmplitude β u a) := by
  unfold dispersionAmplitude
  exact (continuous_const.mul (continuous_normTwist a)).mul continuous_const

lemma continuous_smoothedDispersionVariance (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a) (β : Eisenstein → ℂ)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V)
    {A : ℝ} (hA : 0 < A) : Continuous (fun u => smoothedDispersionVariance S β u V A) := by
  simp_rw [smoothedDispersionVariance_gram S hS β _ V hV hV' hA]
  apply continuous_finsetSum
  intro a ha
  apply continuous_finsetSum
  intro b hb
  exact ((continuous_dispersionAmplitude β a).mul (continuous_dispersionAmplitude β b).star).mul continuous_const

lemma continuous_coprimeDispersionGram (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (V : ℝ → ℂ) (A : ℝ) : Continuous (fun u => coprimeDispersionGram S β u V A) := by
  unfold coprimeDispersionGram
  apply continuous_finsetSum
  intro a ha
  apply continuous_finsetSum
  intro b hb
  split_ifs
  · exact ((continuous_dispersionAmplitude β a).mul (continuous_dispersionAmplitude β b).star).mul continuous_const
  · exact continuous_const

lemma divisorDispersionVariance_one (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (V : ℝ → ℂ) (A : ℝ) :
    divisorDispersionVariance 1 S β u V A = smoothedDispersionVariance S β u V A := by
  simp only [divisorDispersionVariance,smoothedDispersionVariance,one_pow,one_dvd,and_true]

lemma divisorCoprimeDispersionGram_one (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a) (β : Eisenstein → ℂ) (u : ℝ) (V : ℝ → ℂ) (A : ℝ) :
    divisorCoprimeDispersionGram 1 S β u V A = coprimeDispersionGram S β u V A := by
  unfold divisorCoprimeDispersionGram
  rw [norm_one_eq,one_pow,div_one]
  unfold coprimeDispersionGram
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have hca : cubicSymbol a 1 = 1 := (cubic_reciprocity (hS a ha) primary_one).trans (cubicSymbol_one_lower a)
  have hcb : cubicSymbol b 1 = 1 := (cubic_reciprocity (hS b hb) primary_one).trans (cubicSymbol_one_lower b)
  simp only [dispersionAmplitude,divisorTwistedCoefficient,one_pow,hca,hcb,star_one,mul_one]

end CubicFirstMoment

end

end OAI
