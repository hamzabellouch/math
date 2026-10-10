import OAI.NumberTheory.CubicMoment.Estimates.CommonGramRemainder
import OAI.NumberTheory.CubicMoment.Estimates.HeightGramContinuity

namespace OAI

/-! The full variance is the exact sum of all common-factor blocks. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma primaryMass_eq_commonGram (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a) (v : Eisenstein → ℂ)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V)
    {A : ℝ} (hA : 0 < A) :
    primarySmoothedSieveMass S v V A = ∑ k ∈ commonRowFactors S, commonGramBlock S v V A k := by
  rw [primarySmoothedSieveMass_gram S (fun a ha => (hS a ha).1) v V hV hV' hA]
  exact common_factor_matrix_decomposition S hS
    (fun a b => v a*star (v b)*primaryCharacterGram a b V A)

lemma smoothedVariance_eq_commonGram (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a) (β : Eisenstein → ℂ) (u : ℝ)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V)
    {A : ℝ} (hA : 0 < A) :
    smoothedDispersionVariance S β u V A = ∑ k ∈ commonRowFactors S,
      commonGramBlock S (fun b => star (dispersionAmplitude β u b)) V A k := by
  have he : smoothedDispersionVariance S β u V A =
      primarySmoothedSieveMass S (fun b => star (dispersionAmplitude β u b)) V A := by
    unfold smoothedDispersionVariance primarySmoothedSieveMass
    apply tsum_congr
    intro a
    rw [dispersionPolynomial_conj,norm_star]
  exact he.trans (primaryMass_eq_commonGram S hS _ V hV hV' hA)

lemma dispersionAmplitude_norm_squarefree {b : Eisenstein} (hb : primary b)
    (hs : Squarefree b) (β : Eisenstein → ℂ) (u : ℝ) :
    ‖dispersionAmplitude β u b‖ = ‖β b‖ := by
  simp only [dispersionAmplitude,norm_mul,norm_normTwist,norm_gauss hb,
    ite_eq_left hs,mul_one]

end CubicFirstMoment

end

end OAI
