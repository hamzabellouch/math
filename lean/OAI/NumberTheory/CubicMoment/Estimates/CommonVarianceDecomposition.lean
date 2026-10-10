import OAI.NumberTheory.CubicMoment.Estimates.CommonDispersionPoisson
import OAI.NumberTheory.CubicMoment.Estimates.DivisorCoprimePoisson

namespace OAI

/-! The square-divisor variance as actual character mass, followed by
its canonical common-factor decomposition. This is the bridge to the
wide dual recurrence on shortened rows. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def divisorGramCoefficient (d : Eisenstein) (β : Eisenstein → ℂ) (u : ℝ)
    (a : Eisenstein) : ℂ := star (dispersionAmplitude (divisorTwistedCoefficient d β) u a)

lemma divisorGramCoefficient_norm_le (d : Eisenstein) (β : Eisenstein → ℂ) (u : ℝ)
    {a : Eisenstein} (ha : primary a) : ‖divisorGramCoefficient d β u a‖ ≤ ‖β a‖ := by
  simp only [divisorGramCoefficient,norm_star,dispersionAmplitude,norm_mul,
    norm_normTwist,mul_one,divisorTwistedCoefficient,norm_star]
  have hg := norm_gauss_le_one ha
  have hc := norm_cubicSymbol_le_one ha (d^2)
  calc
    _ ≤ ‖β a‖*1*1 := by gcongr
    _ = _ := by ring

lemma divisorDispersionVariance_eq_primaryMass {d : Eisenstein} (hd : primary d)
    (S : Finset Eisenstein) (hS : ∀ a ∈ S, primary a)
    (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) {A : ℝ} (hA : 0 < A) :
    divisorDispersionVariance d S β u W A =
      primarySmoothedSieveMass S (divisorGramCoefficient d β u) W (A/(norm d)^2) := by
  have hdN := norm_pos_of_ne_zero (primary_ne_zero hd)
  rw [divisorDispersionVariance_scaled hd S hS β u W hW hW' hA,
    primarySmoothedSieveMass_gram S hS _ W hW hW' (by positivity)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  simp only [divisorGramCoefficient,dispersionAmplitude,divisorTwistedCoefficient,
    mixedSymbol,star_mul,star_star]
  ring

 theorem divisorDispersionVariance_common_grams {d : Eisenstein} (hd : primary d)
    (S : Finset Eisenstein) (hS : ∀ a ∈ S, primary a ∧ Squarefree a)
    (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) {A : ℝ} (hA : 0 < A) :
    divisorDispersionVariance d S β u W A =
      ∑ k ∈ commonRowFactors S, ∑ s ∈ (primaryPrimeFactors k).powerset,
        let m := ∏ p ∈ s, p
        (idealMoebius m:ℂ)*coprimeGramForm (residualRows S k)
          (commonBlockCoefficient (divisorGramCoefficient d β u) k m)
          W (A/(norm d)^2/norm m) := by
  have hdN := norm_pos_of_ne_zero (primary_ne_zero hd)
  rw [divisorDispersionVariance_eq_primaryMass hd S (fun a ha => (hS a ha).1)
    β u W hW hW' hA]
  exact primarySmoothedSieveMass_common_blocks S hS _ W hW hW' (by positivity)

end CubicFirstMoment

end

end OAI
