import OAI.NumberTheory.CubicMoment.Estimates.SievedDispersion
import OAI.NumberTheory.CubicGram.CommonRows

namespace OAI

/-! The full square-divisor variance in canonical common-factor Poisson
coordinates. The existing prime-set reindexing constructs all residuals. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def divisorCommonPoissonBlock (d k : Eisenstein) (S : Finset Eisenstein)
    (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ) (A : ℝ) : ℂ :=
  ∑ a ∈ residualRows S k, ∑ b ∈ residualRows S k, if IsCoprime a b then
    ∑ s ∈ (primaryPrimeFactors k).powerset,
      let m := ∏ p ∈ s, p
      mixedSymbol (k*b) (k*a) (d^2)*
        (β (k*a)*star (β (k*b))*normTwist u (k*a)*star (normTwist u (k*b))*
          mixedCubic b a k*(idealMoebius m:ℂ)*mixedCubic b a m*
            (((A/(norm d)^2/norm m)/(9*Real.sqrt (norm (b*a)))):ℝ)*
              ∑' h : Eisenstein, gramDualTerm b a W (A/(norm d)^2/norm m) h)
    else 0

theorem divisorDispersionVariance_poisson {d : Eisenstein} (hd : primary d)
    (S : Finset Eisenstein) (hS : ∀ a ∈ S, primary a ∧ Squarefree a)
    (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) {A : ℝ} (hA : 0 < A) :
    divisorDispersionVariance d S β u W A =
      ∑ k ∈ commonRowFactors S, divisorCommonPoissonBlock d k S β u W A := by
  rw [divisorDispersionVariance_gram d S (fun a ha => (hS a ha).1) β u W hW hW' hA,
    common_factor_matrix_decomposition S hS]
  apply Finset.sum_congr rfl
  intro k hkS
  have hk := commonRowFactors_spec hS hkS
  have hr := residualRows_primary hk.1 hS
  unfold divisorCommonPoissonBlock
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : IsCoprime a b
  · simp only [ite_eq_left hab]
    exact divisor_dispersion_common_pair_poisson hd hk.1 (hr a ha).1 (hr b hb).1
      hk.2 (hr a ha).2 (hr b hb).2 hab β u W hW hW' hA
  · simp only [ite_eq_right hab]

end CubicFirstMoment

end

end OAI
