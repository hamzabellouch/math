import OAI.Probability.InvariantIsing.Cavity.CavityFactorBlockProjection

namespace OAI

/-! Weak convergence of the actual random cavity factor coefficients,
obtained from the joint Haar compression theorem. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix BoundedContinuousFunction

namespace InvariantIsing

theorem cavityHaarFactorCoefficients_integral_tendsto {m n d : ℕ}
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
    (F : CavityFactorBlocks d n →ᵇ ℝ) :
    Tendsto (fun k => ∫ U, F (cavityCompressionFactorBlocks e lam lam₀ B₀
      (fun a => cavityWindowGram
        ((U : Matrix (Fin (N k)) (Fin (N k)) ℝ) * A₀ k) (l a k) (u a k))) ∂μ k)
      atTop (𝓝 (F (cavitySmallFactorBlocks (cavityRepeatedSpectrum (n := n) lam)
        (Matrix.diagonal lam₀) (fun i j => B₀ (e i) j)
        (cavitySpectralStack (fun a => (ρu a - ρl a) • 1))))) := by
  let D := cavityRepeatedSpectrum (n := n) lam
  let A := Matrix.diagonal lam₀
  let G := F.compContinuous ⟨cavityFactorBlocksFromMatrix A,
    continuous_cavityFactorBlocksFromMatrix A⟩
  have h := cavityHaarCompressionBlocks_integral_tendsto e
    (D.submatrix e.symm e.symm) B₀ hB₀ N l u hN hu hl hlu hle hue
    ρl ρu hρ hρl hρu hEB μ A₀ hA₀ G
  have heq (M : Fin m → Matrix (Fin n) (Fin n) ℝ) :
      G (cavityCompressionBlocks e (D.submatrix e.symm e.symm) B₀ M) =
        F (cavityCompressionFactorBlocks e lam lam₀ B₀ M) := by
    exact congrArg F (cavityCompressionFactorBlocks_eq_projection e lam lam₀ B₀ M).symm
  have hb : (Matrix.submatrix (fun i j => B₀ (e i) j) e.symm id) = B₀ := by
    ext i j
    exact congrArg (fun k => B₀ k j) (e.apply_symm_apply i)
  have hp := cavitySmallFactorBlocks_reindex e D A (fun i j => B₀ (e i) j)
    (cavitySpectralStack (fun a => (ρu a - ρl a) • 1))
  rw [hb] at hp
  have hlimit : G (cavitySpecialBlocks (D.submatrix e.symm e.symm) B₀
      (cavityReindexedStack e (fun a => (ρu a - ρl a) • 1))) =
      F (cavitySmallFactorBlocks D A (fun i j => B₀ (e i) j)
        (cavitySpectralStack (fun a => (ρu a - ρl a) • 1))) := by
    change F (cavitySmallFactorBlocks (D.submatrix e.symm e.symm) A B₀
      (cavityReindexedStack e (fun a => (ρu a - ρl a) • 1))) = _
    exact congrArg F hp
  simpa only [heq, hlimit] using h

end InvariantIsing

end

end OAI
