import OAI.NumberTheory.CubicMoment.Estimates.DispersionCommonFactors
import OAI.NumberTheory.CubicMoment.Estimates.GramOperator
import OAI.NumberTheory.CubicGram.LatticeCounts

namespace OAI

/-!
# Dispersion after a square-divisor restriction

The squarefree majorant introduces `d² ∣ a`. Expanding the actual
variance and changing variables produces a Gram kernel at scale
`A / N(d)²`, with the precise cubic-character factor retained.
-/

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def divisorCharacterGram (d p q : Eisenstein) (W : ℝ → ℂ) (A : ℝ) : ℂ :=
  ∑' a : Eisenstein, if primary a ∧ d^2 ∣ a then
    W (norm a/A)*cubicSymbol p a*star (cubicSymbol q a) else 0

def divisorDispersionVariance (d : Eisenstein) (B : Finset Eisenstein)
    (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ) (A : ℝ) : ℂ :=
  ∑' a : Eisenstein, if primary a ∧ d^2 ∣ a then
    W (norm a/A)*((‖dispersionPolynomial B β u a‖^2 : ℝ) : ℂ) else 0

lemma divisorCharacterGram_scale {d p q : Eisenstein}
    (hd : primary d) (hp : primary p) (hq : primary q)
    (W : ℝ → ℂ) (A : ℝ) :
    divisorCharacterGram d p q W A =
      mixedSymbol p q (d^2)*primaryCharacterGram p q W (A/(norm d)^2) := by
  have hd2 : primary (d^2) := by simpa only [pow_two] using primary_mul hd hd
  have he := primaryCharacterGram_divisor_scale hp hq hd2 W A
  simpa only [divisorCharacterGram,pow_two,norm_mul_eq] using he

/-- The restricted variance is still the exact finite Gram quadratic form. -/
theorem divisorDispersionVariance_gram (d : Eisenstein) (B : Finset Eisenstein)
    (hB : ∀ b ∈ B, primary b) (β : Eisenstein → ℂ) (u : ℝ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {A : ℝ} (hA : 0 < A) :
    divisorDispersionVariance d B β u W A =
      ∑ p ∈ B, ∑ q ∈ B, dispersionAmplitude β u p*star (dispersionAmplitude β u q)*
        divisorCharacterGram d q p W A := by
  let H (p q a : Eisenstein) : ℂ := dispersionAmplitude β u p*star (dispersionAmplitude β u q)*
    (if primary a ∧ d^2 ∣ a then W (norm a/A)*cubicSymbol q a*star (cubicSymbol p a) else 0)
  have hsum (p : Eisenstein) (hp : p ∈ B) (q : Eisenstein) (hq : q ∈ B) :
      Summable (H p q) := by
    apply Summable.mul_left
    exact summable_gram_restricted (hB q hq) (hB p hp) W hW hW' hA (fun a => d^2 ∣ a)
  have hpoint (a : Eisenstein) :
      (if primary a ∧ d^2 ∣ a then W (norm a/A)*
        ((‖dispersionPolynomial B β u a‖^2 : ℝ) : ℂ) else 0) =
      ∑ p ∈ B, ∑ q ∈ B, H p q a := by
    by_cases ha : primary a ∧ d^2 ∣ a
    · simp only [H,ite_eq_left ha,dispersionPolynomial]
      change W (norm a/A)*((‖∑ p ∈ B, dispersionAmplitude β u p*star (cubicSymbol p a)‖^2 : ℝ) : ℂ) = _
      rw [complex_sum_norm_sq_expansion,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      simp only [star_mul,star_star]
      ring
    · simp [ha,H]
  unfold divisorDispersionVariance
  simp_rw [hpoint]
  rw [Summable.tsum_finsetSum (fun p hp => summable_sum (fun q hq => hsum p hp q hq))]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Summable.tsum_finsetSum (hsum p hp)]
  apply Finset.sum_congr rfl
  intro q hq
  exact tsum_mul_left

/-- The `d²` restriction has norm cost `N(d)²` and the expected character
phase. No coprimality condition is dropped in this identity. -/
theorem divisorDispersionVariance_scaled {d : Eisenstein} (hd : primary d)
    (B : Finset Eisenstein) (hB : ∀ b ∈ B, primary b) (β : Eisenstein → ℂ) (u : ℝ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {A : ℝ} (hA : 0 < A) :
    divisorDispersionVariance d B β u W A =
      ∑ p ∈ B, ∑ q ∈ B, dispersionAmplitude β u p*star (dispersionAmplitude β u q)*
        mixedSymbol q p (d^2)*primaryCharacterGram q p W (A/(norm d)^2) := by
  rw [divisorDispersionVariance_gram d B hB β u W hW hW' hA]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  rw [divisorCharacterGram_scale hd (hB q hq) (hB p hp) W A]
  ring

/-- Exact off-diagonal Poisson formula after the square-divisor sieve.
The fixed `d²` character factor is retained even when it vanishes. -/
theorem divisor_dispersion_common_pair_poisson {d k a b : Eisenstein}
    (hd : primary d) (hk : primary k) (ha : primary a) (hb : primary b)
    (hsk : Squarefree k) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (β : Eisenstein → ℂ) (u : ℝ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {A : ℝ} (hA : 0 < A) :
    dispersionAmplitude β u (k*a) * star (dispersionAmplitude β u (k*b)) *
      divisorCharacterGram d (k*b) (k*a) W A =
      ∑ s ∈ (primaryPrimeFactors k).powerset,
        let m := ∏ p ∈ s, p
        mixedSymbol (k*b) (k*a) (d^2) *
          (β (k*a) * star (β (k*b)) * normTwist u (k*a) * star (normTwist u (k*b)) *
          mixedCubic b a k * (idealMoebius m : ℂ) * mixedCubic b a m *
            (((A / (norm d)^2 / norm m) / (9 * Real.sqrt (norm (b*a)))) : ℝ) *
              ∑' h : Eisenstein, gramDualTerm b a W (A / (norm d)^2 / norm m) h) := by
  have hscale : 0 < A / (norm d)^2 :=
    div_pos hA (sq_pos_of_pos (norm_pos_of_ne_zero (primary_ne_zero hd)))
  rw [divisorCharacterGram_scale hd (primary_mul hk hb) (primary_mul hk ha)]
  calc
    _ = mixedSymbol (k*b) (k*a) (d^2) *
        (dispersionAmplitude β u (k*a) * star (dispersionAmplitude β u (k*b)) *
          primaryCharacterGram (k*b) (k*a) W (A/(norm d)^2)) := by ring
    _ = _ := by
      rw [dispersion_common_pair_poisson hk ha hb hsk hsa hsb hab β u W hW hW' hscale,
        Finset.mul_sum]

end CubicFirstMoment

end

end OAI
