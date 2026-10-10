import OAI.Probability.InvariantIsing.Cavity.CavityHaarFactorCoefficients
import OAI.Probability.InvariantIsing.Cavity.CavityCoefficientProbability

namespace OAI

/-! The actual Haar cavity coefficients concentrate at the deterministic
finite-spectrum coefficients, in the metric used by the replica bounds. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix BoundedContinuousFunction

namespace InvariantIsing

theorem cavityHaarFactorCoefficients_probability {m n d : ℕ}
    (e : Fin (m*n) ≃ Fin (d+n)) (lam : Fin m → ℝ) (lam₀ : Fin d → ℝ)
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (hB₀ : B₀.transpose * B₀ = 1)
    (N : ℕ → ℕ) (l u : Fin m → ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hu : ∀ a, Tendsto (u a) atTop atTop)
    (hl : ∀ a, (∀ k, l a k = 0) ∨ Tendsto (l a) atTop atTop)
    (hlu : ∀ a k, l a k ≤ u a k)
    (hle : ∀ a k, l a k ≤ N k) (hue : ∀ a k, u a k ≤ N k)
    (ρl ρu : Fin m → ℝ) (hρ : ∀ a, 0 ≤ ρu a - ρl a)
    (hρl : ∀ a, Tendsto (fun k => (l a k : ℝ) / N k) atTop (𝓝 (ρl a)))
    (hρu : ∀ a, Tendsto (fun k => (u a k : ℝ) / N k) atTop (𝓝 (ρu a)))
    (hEB : (cavityReindexedStack e (fun a => (ρu a - ρl a) • 1)).transpose * B₀ = 0)
    (μ : (k : ℕ) → Measure (Orthogonal (N k)))
    [∀ k, IsProbabilityMeasure (μ k)] [∀ k, (μ k).IsMulRightInvariant]
    (A₀ : (k : ℕ) → Matrix (Fin (N k)) (Fin n) ℝ)
    (hA₀ : ∀ k, (A₀ k).transpose * A₀ k = 1)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun k => (μ k).real {U | δ < cavityFactorDeviation
      (cavityCompressionFactorBlocks e lam lam₀ B₀ (fun a => cavityWindowGram
        ((U : Matrix (Fin (N k)) (Fin (N k)) ℝ) * A₀ k) (l a k) (u a k)))
      (cavitySmallFactorBlocks (cavityRepeatedSpectrum (n := n) lam)
        (Matrix.diagonal lam₀) (fun i j => B₀ (e i) j)
        (cavitySpectralStack (fun a => (ρu a - ρl a) • 1)))}) atTop (𝓝 0) := by
  let A := fun k (U : Orthogonal (N k)) => cavityCompressionFactorBlocks e lam lam₀ B₀
    (fun a => cavityWindowGram ((U : Matrix (Fin (N k)) (Fin (N k)) ℝ) * A₀ k) (l a k) (u a k))
  have hA k : Measurable (A k) := by
    apply (measurable_cavityCompressionFactorBlocks e lam lam₀ B₀).comp
    apply measurable_pi_iff.mpr
    intro a
    exact (continuous_cavityWindowGram (N k) n (l a k) (u a k)).measurable.comp
      (continuous_subtype_val.matrix_mul continuous_const).measurable
  exact cavity_factor_coefficients_probability μ A hA _
    (fun F => cavityHaarFactorCoefficients_integral_tendsto e lam lam₀ B₀ hB₀
      N l u hN hu hl hlu hle hue ρl ρu hρ hρl hρu hEB μ A₀ hA₀ F) hδ

end InvariantIsing

end

end OAI
