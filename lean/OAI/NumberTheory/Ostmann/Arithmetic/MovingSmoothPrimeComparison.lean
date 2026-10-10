import OAI.NumberTheory.Ostmann.Arithmetic.SmoothPrimeComparison
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSmoothPolynomials

namespace OAI

/-! # Published prime comparison for the full moving smooth factor -/

namespace Ostmann
open MeasureTheory
open scoped SchwartzMap

/-- The actual moving Fourier leaves and all logarithmic node cutoffs have
one uniform prime-to-Page comparison. The cut set has at most one derivative
root per leaf; the error contains no mesh count and no node-center factor. -/
theorem moving_smooth_prime_comparison {σ : Type*} (value : σ → ℕ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hL : L.natDegree ≤ 1) (hR : R.natDegree ≤ 1)
    (hV : T.Frequencies (fun s => |(s : ℝ)| ≤ V)) (φ : ℝ → ℝ)
    (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) :
    ∃ S : Finset ℝ, S.card ≤ 2 ^ n ∧
      ∀ (P : PublishedProgressionInput) (Q q a : ℕ),
      2 ≤ Q → 1 ≤ q → q ≤ Q → a.Coprime q →
      ∀ u v : ℝ, 1 ≤ u → u ≤ v → v ≤ u + 1 →
      rootCellCode S (Real.exp u) = rootCellCode S (Real.exp v) →
      ‖complexPrimeInterval q a u v (fun y => smoothPolynomialWeight
          (movingSmoothPolynomialFactors value T L R ψ X lo hi hlo hhi φ G B D hB hD hφ hlip)
          (Real.exp y)) -
        ∫ y in Set.Ioc u v, smoothPolynomialWeight
          (movingSmoothPolynomialFactors value T L R ψ X lo hi hlo hhi φ G B D hB hD hφ hlip)
          (Real.exp y) * (selectedPrimeLogDensity P Q q a y : ℂ)‖ ≤
        (movingFourierVariationBudget ψ V lo hi n *
          (2 * B + D * (Real.exp 2 - 1)) ^ (2 ^ n - 1)) *
        (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt u) +
          Real.exp (-P.kappa * u / Real.log (4 * (Q : ℝ)))) := by
  obtain ⟨S, hcard, hvar⟩ := movingSmoothPolynomialFactors_variation value T L R ψ X lo hi V
    hlo hhi hL hR hV φ G B D hB hD hφ hlip
  refine ⟨S, hcard, ?_⟩
  intro P Q q a hQ hq hqQ ha u v hu huv hshort hcode
  apply P.continuous_prime_comparison hQ hq hqQ ha u v hu huv hshort _
    ((continuous_smoothPolynomialWeight _).comp Real.continuous_exp).continuousOn
  intro s hs N hs0 hsN
  apply hvar (fun j => Real.exp (s j)) (Real.exp_monotone.comp hs) N
  have hlo' : Real.exp u ≤ Real.exp (s (N - 1)) := by
    rw [← hs0]
    exact Real.exp_le_exp.mpr (hs (Nat.zero_le _))
  have hhi' : Real.exp (s (N - 1)) ≤ Real.exp v := by
    rw [← hsN]
    exact Real.exp_le_exp.mpr (hs (Nat.sub_le _ _))
  rw [hs0]
  exact (rootCellCode_convex S hlo' hhi' hcode).symm

end Ostmann

end OAI
