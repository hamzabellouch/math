import OAI.NumberTheory.CubicMoment.Estimates.DivisorDispersion
import OAI.NumberTheory.CubicMoment.Estimates.SieveMobius

namespace OAI

/-!
# Exact assembly of the sieved dispersion variance

The positive majorant is the finite sum of the square-divisor variances.
This makes the collected coefficients and the restricted Poisson formula
apply to the original arithmetic polynomial.
-/

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma norm_dispersionPolynomial_le (B : Finset Eisenstein)
    (hB : ∀ b ∈ B, primary b) (β : Eisenstein → ℂ) (u : ℝ) (a : Eisenstein) :
    ‖dispersionPolynomial B β u a‖ ≤ ∑ b ∈ B, ‖dispersionAmplitude β u b‖ := by
  apply (norm_sum_le B _).trans
  apply Finset.sum_le_sum
  intro b hb
  rw [norm_mul,norm_star]
  exact mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_cubicSymbol_le_one (hB b hb) a)

lemma summable_restricted_dispersion (P : Eisenstein → Prop) (B : Finset Eisenstein)
    (hB : ∀ b ∈ B, primary b) (β : Eisenstein → ℂ) (u : ℝ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {A : ℝ} (hA : 0 < A) :
    Summable (fun a : Eisenstein => if primary a ∧ P a then
      W (norm a/A)*((‖dispersionPolynomial B β u a‖^2 : ℝ) : ℂ) else 0) := by
  let R := ∑ b ∈ B, ‖dispersionAmplitude β u b‖
  have hs := (schwartz_summable_eisenstein (normProfileSchwartz W hW hW' A hA)).norm
  apply (hs.mul_right (R^2)).of_norm_bounded
  intro a
  change ‖ite _ _ _‖ ≤ ‖W (norm a/A)‖*R^2
  split_ifs with ha
  · rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
    apply mul_le_mul_of_nonneg_left _ (_root_.norm_nonneg _)
    exact pow_le_pow_left₀ (_root_.norm_nonneg _) (norm_dispersionPolynomial_le B hB β u a) 2
  · rw [norm_zero]
    positivity

def sievedDispersionVariance (C B : Finset Eisenstein) (β : Eisenstein → ℂ)
    (u : ℝ) (W : ℝ → ℂ) (A : ℝ) : ℂ :=
  ∑' a : Eisenstein, if primary a then
    (((truncatedSquareDivisorSum C a)^2 : ℝ) : ℂ)*
      W (norm a/A)*((‖dispersionPolynomial B β u a‖^2 : ℝ) : ℂ) else 0

/-- Exact finite assembly: no error term is introduced when the
squarefree positive majorant is collected by its square divisor. -/
theorem sievedDispersionVariance_eq (C : Finset Eisenstein)
    (hC : ∀ c ∈ C, primary c ∧ Squarefree c)
    (B : Finset Eisenstein) (hB : ∀ b ∈ B, primary b)
    (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) {A : ℝ} (hA : 0 < A) :
    sievedDispersionVariance C B β u W A =
      ∑ d ∈ (C.product C).image (fun t => primarySquarefreeJoin t.1 t.2),
        (collectedSquarefreeSieveCoefficient C d : ℂ)*
          divisorDispersionVariance d B β u W A := by
  let E := (C.product C).image (fun t => primarySquarefreeJoin t.1 t.2)
  let H (d a : Eisenstein) : ℂ :=
    (collectedSquarefreeSieveCoefficient C d : ℂ) *
      (if primary a ∧ d^2 ∣ a then
        W (norm a/A)*((‖dispersionPolynomial B β u a‖^2 : ℝ) : ℂ) else 0)
  have hs (d : Eisenstein) : Summable (H d) :=
    (summable_restricted_dispersion (fun a => d^2 ∣ a) B hB β u W hW hW' hA).mul_left _
  have hp (a : Eisenstein) :
      (if primary a then (((truncatedSquareDivisorSum C a)^2 : ℝ) : ℂ)*
        W (norm a/A)*((‖dispersionPolynomial B β u a‖^2 : ℝ) : ℂ) else 0) =
        ∑ d ∈ E, H d a := by
    by_cases ha : primary a
    · rw [ite_eq_left ha]
      have hc := congrArg (fun x : ℝ => (x : ℂ)) (truncatedSquareDivisorSum_collected C hC a)
      push_cast at hc
      rw [Complex.ofReal_pow,hc,Finset.sum_mul,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      dsimp only [H]
      by_cases hd' : d^2 ∣ a <;> simp [ha,hd',mul_assoc]
    · simp [ha,H]
  unfold sievedDispersionVariance
  simp_rw [hp]
  rw [Summable.tsum_finsetSum (fun d _ => hs d)]
  apply Finset.sum_congr rfl
  intro d hd
  exact tsum_mul_left

end CubicFirstMoment

end

end OAI
