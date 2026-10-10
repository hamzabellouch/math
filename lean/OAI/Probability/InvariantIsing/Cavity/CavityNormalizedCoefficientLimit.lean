import OAI.Probability.InvariantIsing.Cavity.CavityProjectorCoefficientError
import OAI.Probability.InvariantIsing.Cavity.CavityCoefficientValueLimit

namespace OAI

/-! Actual normalized projector-cavity tests tolerate random coefficient
replacement in probability. No moment or inverse-partition assumption
is added on a fixed spatial cutoff. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology Matrix

namespace InvariantIsing

theorem cavity_normalized_coefficient_tendsto
    {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]
    {m d n : ℕ} (N depth : ℕ → ℕ)
    (g : (k : ℕ) → Fin (N k) → Fin m)
    (P : (k : ℕ) → Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (T : (k : ℕ) → LabeledTree (depth k)) (lam v : Fin m → ℝ)
    (u : ℕ → ℝ) (hu : ∀ j, |u j| ≤ 2) (t : ℝ) {D : ℝ} (hD : 0 ≤ D)
    (A : (k : ℕ) → Ω k → CavityFactorBlocks d n) (hA : ∀ k, Measurable (A k))
    (A₀ : CavityFactorBlocks d n)
    (p : (k : ℕ) → Ω k → CavityProjectorFrame (N k) m d)
    (hp : ∀ k, Measurable (p k))
    (hprojector : ∀ k ω, ∃ V : Orthogonal (N k),
      (p k ω).1 = fun a => cavitySpectralProjector V (cavitySpectralGroup (g k) a))
    (F : (k : ℕ) → Ω k → (Fin 2 → (Spin (N k) × LabeledLeaf (depth k)) × Spin n) → ℝ)
    (hF : ∀ k, Measurable (Function.uncurry (F k)))
    {M : ℝ} (hM : 0 ≤ M) (hFb : ∀ k ω σ, |F k ω σ| ≤ M)
    (hprob : ∀ δ > 0, Tendsto (fun k => (P k).real
      {ω | δ < cavityFactorDeviation (A k ω) A₀}) atTop (𝓝 0)) :
    Tendsto (fun k =>
      (∫ ω, cavityProjectorCavityMean (T k)
        (fun a => t*lam a+2*perturbationScale (N k)*v a) u t D (A k ω) (F k ω) (p k ω) ∂P k) -
      ∫ ω, cavityProjectorCavityMean (T k)
        (fun a => t*lam a+2*perturbationScale (N k)*v a) u t D A₀ (F k ω) (p k ω) ∂P k)
      atTop (𝓝 0) := by
  apply cavity_coefficient_values_tendsto P A hA A₀ _ _
    (fun k => measurable_cavityProjectorCavityMean (T k) _ u t D (A k) (hA k) (p k) (hp k) (F k) (hF k))
    (fun k => measurable_cavityProjectorCavityMean (T k) _ u t D (fun _ => A₀) measurable_const
      (p k) (hp k) (F k) (hF k)) hM
    (show 0 ≤ 4*|t| *D by positivity)
    (fun k ω => by simpa only [← Real.norm_eq_abs] using
      cavityProjectorCavityMean_bound (T k) _ u t D (A k ω) (F k ω) hM (hFb k ω) (p k ω))
    (fun k ω => by simpa only [← Real.norm_eq_abs] using
      cavityProjectorCavityMean_bound (T k) _ u t D A₀ (F k ω) hM (hFb k ω) (p k ω))
    _ hprob
  intro k ω s hs
  obtain ⟨V,hV⟩ := hprojector k ω
  have hb := cavity_projector_coefficient_error (g k) V (T k) lam v u hu t hD
    (A k ω) A₀ (p k ω) hV (F k ω) hM (hFb k ω) hs
  convert hb using 1
  ring

end InvariantIsing

end

end OAI
