import OAI.Geometry.SurfaceImmersion.Correction.PolynomialMeanIteration

namespace OAI

/-! An explicit polynomial threshold for the actual finite mean trial.
Only finitely many input orders affect the power in the threshold. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseMean
open RealModes FiniteMean WeightedEstimates

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem finite_mean_polynomial_threshold (L : ℕ) (p : ℕ → ℕ) (C : ℕ → ℝ)
    (G H : ℕ → ℝ → ℝ) (hC : ∀ m, 0 ≤ C m)
    (hG : ∀ m, HasPolynomialBound (G m)) (hH : ∀ m, HasPolynomialBound (H m)) (n : ℕ) :
    ∃ d : ℕ, ∃ A : ℝ, 1 ≤ A ∧ ∀ x : ℝ, 1 ≤ x →
    ∀ {U : Set E}, UniqueDiffOn ℝ U → ∀ {s : ℝ}, 0 ≤ s →
    ∀ {reference f : E → F} {r0 r1 : ℝ}, r0 < r1 →
    ∀ {T : ℝ → (E → F) → E → F},
      MeanBounds U s reference r1 L T
        (polynomialMeanProfile p C (fun m => G m x))
        (polynomialMeanProfile p C (fun m => G m x)) →
      (∀ m, 1 ≤ H m x) → ContDiffOn ℝ ∞ f U →
      (∀ y ∈ U, ‖f y-reference y‖ ≤ r0) →
      (∀ m, WeightedBound U s m (H m x) f) →
      0 < min 1 ((r1-r0)/(2*(A*x^d))) ∧
      ∀ η : ℝ, 0 < η → η ≤ min 1 ((r1-r0)/(2*(A*x^d))) →
      ∀ j ≤ n, ContDiffOn ℝ ∞ (trial f T η j) U ∧
        InTrialBall U reference r1 (trial f T η j) ∧
        (∀ m, WeightedBound U s m (polynomialMeanSize L p C G H j m x) (trial f T η j)) ∧
        (∀ m, WeightedBound U s m (polynomialMeanDifference L p C G H j m x*η^(j+1))
          (trial f T η j+T η (trial f T η j)-f)) := by
  obtain ⟨d,A,hA,hvalue⟩ := polynomialMean_threshold_budget L p C G H hC hG hH n
  refine ⟨d,A,hA,?_⟩
  intro x hx U hU s hs reference f r0 r1 hgap T hT hH1 hf hnear hnorm
  exact finite_substitution_with_threshold hU hs hgap hT hH1 hf hnear hnorm n
    (mul_pos (zero_lt_one.trans_le hA) (pow_pos (zero_lt_one.trans_le hx) d)) (hvalue x hx)

end ClosedSurfaceR4.PhaseMean

end

end OAI
