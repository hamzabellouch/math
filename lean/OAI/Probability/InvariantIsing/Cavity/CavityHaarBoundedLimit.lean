import OAI.Probability.InvariantIsing.Cavity.CavityCompressionBlocks

namespace OAI

/-! Transfer bounded measurable cutoff limits from the normalized
Gaussian frame to the actual Haar frame. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology Matrix

namespace InvariantIsing

theorem cavityHaarWindowGram_bounded_limit {q : ℕ}
    (N l u : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (μ : (k : ℕ) → Measure (Orthogonal (N k)))
    [∀ k, IsProbabilityMeasure (μ k)] [∀ k, (μ k).IsMulRightInvariant]
    (A₀ : (k : ℕ) → Matrix (Fin (N k)) (Fin q) ℝ)
    (hA₀ : ∀ k, (A₀ k).transpose * A₀ k = 1)
    (F : ℕ → Matrix (Fin q) (Fin q) ℝ → ℝ) (hF : ∀ k, Measurable (F k))
    {C a : ℝ} (hb : ∀ k M, |F k M| ≤ C)
    (hlim : ∀ᵐ x ∂cavityGaussianRows q,
      Tendsto (fun k => F k (cavityWindowGram
        (cavityNormalizeFrame (cavityGaussianMatrix x (N k))) (l k) (u k)))
        atTop (𝓝 a)) :
    Tendsto (fun k => ∫ U, F k (cavityWindowGram
      ((U : Matrix (Fin (N k)) (Fin (N k)) ℝ) * A₀ k) (l k) (u k)) ∂μ k)
      atTop (𝓝 a) := by
  let f := fun k (x : ℕ → Fin q → ℝ) => F k (cavityWindowGram
    (cavityNormalizeFrame (cavityGaussianMatrix x (N k))) (l k) (u k))
  have hfm (k : ℕ) : Measurable (f k) :=
    ((hF k).comp (continuous_cavityWindowGram (N k) q (l k) (u k)).measurable).comp
      (measurable_cavityGaussianNormalizedFrame q (N k))
  have hfi (k : ℕ) : Integrable (f k) (cavityGaussianRows q) :=
    Integrable.of_bound (hfm k).aestronglyMeasurable C
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb k _)
  have hfu : Tendsto (fun k => ∫ x, f k x ∂cavityGaussianRows q) atTop (𝓝 a) := by
    have ht := tendsto_integral_of_dominated_convergence (fun _ : ℕ → Fin q → ℝ => C)
      (fun k => (hfm k).aestronglyMeasurable) (integrable_const _)
      (fun k => ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb k _)
      hlim
    simpa only [integral_const, probReal_univ, one_smul] using ht
  have hdiff := cavity_conditioning_tendsto (cavityGaussianRows q)
    (fun k => cavityGoodGram q (N k)) (fun k => measurableSet_cavityGoodGram q (N k))
    ((cavityGoodGram_probability_tendsto q).comp hN) f hfi C (fun k x => hb k _)
  have hcond : Tendsto (fun k => ∫ x, f k x
      ∂cond (cavityGaussianRows q) (cavityGoodGram q (N k))) atTop (𝓝 a) := by
    convert hdiff.add hfu using 1 <;> simp
  apply hcond.congr'
  filter_upwards [hN.eventually (cavityGoodGram_eventually_positive q)] with k hk
  exact cavityFrame_measurable_integral_eq_haar hk (μ k) (A₀ k) (hA₀ k)
    (fun A => F k (cavityWindowGram A (l k) (u k)))
    ((hF k).comp (continuous_cavityWindowGram (N k) q (l k) (u k)).measurable)

end InvariantIsing

end

end OAI
