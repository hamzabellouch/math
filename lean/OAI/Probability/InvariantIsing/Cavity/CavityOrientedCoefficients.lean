import OAI.Probability.InvariantIsing.Cavity.CavityOrientation
import OAI.Probability.InvariantIsing.Cavity.CavityCompressionFactors
import OAI.Probability.InvariantIsing.Cavity.CavityCoefficientSampling

namespace OAI

/-! The orientation correction used for physical cavity coordinates
preserves the actual random quadratic coefficients, including their
concentration event. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology Matrix

namespace InvariantIsing

lemma measurable_cavityPhysicalFactorBlocks {N n m d : ℕ}
    (e : Fin (m*n) ≃ Fin (d+n)) (lam : Fin m → ℝ) (lam₀ : Fin d → ℝ)
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (g : Fin (N+n) → Fin m) :
    Measurable (fun U : SpecialOrthogonal (N+n) =>
      cavityCompressionFactorBlocks e lam lam₀ B₀
        (cavityCompressionGrams g (cavitySpecialOrthogonal U))) := by
  exact (measurable_cavityCompressionFactorBlocks e lam lam₀ B₀).comp
    ((measurable_cavityCompressionGrams g).comp
      (measurable_subtype_coe.subtype_mk))

theorem cavity_orientation_factor_event {N n m d : ℕ} (hN : 0 < N+n)
    (e : Fin (m*n) ≃ Fin (d+n)) (lam : Fin m → ℝ) (lam₀ : Fin d → ℝ)
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (g : Fin (N+n) → Fin m)
    (μ : Measure (Orthogonal (N+n))) (A₀ : CavityFactorBlocks d n) (δ : ℝ) :
    (μ.map (cavityOrientationLift hN)).real {U |
      δ < cavityFactorDeviation (cavityCompressionFactorBlocks e lam lam₀ B₀
        (cavityCompressionGrams g (cavitySpecialOrthogonal U))) A₀} =
    μ.real {U | δ < cavityFactorDeviation (cavityCompressionFactorBlocks e lam lam₀ B₀
      (cavityCompressionGrams g U)) A₀} := by
  have hp : MeasurePreserving (cavityOrientationLift hN) μ (μ.map (cavityOrientationLift hN)) :=
    ⟨measurable_cavityOrientationLift hN, rfl⟩
  have h := cavity_factor_deviation_pullback μ (μ.map (cavityOrientationLift hN))
    (cavityOrientationLift hN) hp
    (fun U => cavityCompressionFactorBlocks e lam lam₀ B₀
      (cavityCompressionGrams g (cavitySpecialOrthogonal U)))
    (measurable_cavityPhysicalFactorBlocks e lam lam₀ B₀ g) A₀ δ
  simpa only [cavityOrientationLift_compression] using h.symm

theorem cavity_orientation_factor_probability {n m d : ℕ}
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k+n)
    (e : Fin (m*n) ≃ Fin (d+n)) (lam : Fin m → ℝ) (lam₀ : Fin d → ℝ)
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ)
    (g : (k : ℕ) → Fin (N k+n) → Fin m)
    (μ : (k : ℕ) → Measure (Orthogonal (N k+n)))
    (A₀ : CavityFactorBlocks d n)
    (hprob : ∀ δ > 0, Tendsto (fun k => (μ k).real {U |
      δ < cavityFactorDeviation (cavityCompressionFactorBlocks e lam lam₀ B₀
        (cavityCompressionGrams (g k) U)) A₀}) atTop (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun k => ((μ k).map (cavityOrientationLift (hN k))).real {U |
      δ < cavityFactorDeviation (cavityCompressionFactorBlocks e lam lam₀ B₀
        (cavityCompressionGrams (g k) (cavitySpecialOrthogonal U))) A₀}) atTop (𝓝 0) := by
  simpa only [cavity_orientation_factor_event] using hprob δ hδ

end InvariantIsing

end

end OAI
