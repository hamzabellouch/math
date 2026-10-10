import OAI.Probability.InvariantIsing.Cavity.CavityWindowGram

namespace OAI

/-! Haar cavity compressions converge to their spectral proportions.
The proof transfers the almost sure Gaussian Gram limit through the
exact conditioned frame law. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix MatrixOrder Matrix.Norms.L2Operator
  BoundedContinuousFunction

namespace InvariantIsing

lemma measurable_cavityGaussianNormalizedFrame (q N : ℕ) :
    Measurable (fun x : ℕ → Fin q → ℝ =>
      cavityNormalizeFrame (cavityGaussianMatrix x N)) := by
  apply (measurable_cavityNormalizeFrame N q).comp
  apply Measurable.of_eval_matrix
  intro i j
  exact ((measurable_pi_apply j).comp (measurable_pi_apply (i : ℕ))).div_const _

theorem cavityHaarWindowGram_integral_tendsto {q : ℕ}
    (N l u : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hu : Tendsto u atTop atTop) (hl : (∀ k, l k = 0) ∨ Tendsto l atTop atTop)
    (hle : ∀ k, l k ≤ N k) (hue : ∀ k, u k ≤ N k)
    (ρl ρu : ℝ)
    (hρl : Tendsto (fun k => (l k : ℝ) / N k) atTop (𝓝 ρl))
    (hρu : Tendsto (fun k => (u k : ℝ) / N k) atTop (𝓝 ρu))
    (μ : (k : ℕ) → Measure (Orthogonal (N k)))
    [∀ k, IsProbabilityMeasure (μ k)] [∀ k, (μ k).IsMulRightInvariant]
    (A₀ : (k : ℕ) → Matrix (Fin (N k)) (Fin q) ℝ)
    (hA₀ : ∀ k, (A₀ k).transpose * A₀ k = 1)
    (F : Matrix (Fin q) (Fin q) ℝ →ᵇ ℝ) :
    Tendsto (fun k => ∫ U, F (cavityWindowGram
      ((U : Matrix (Fin (N k)) (Fin (N k)) ℝ) * A₀ k) (l k) (u k)) ∂μ k)
      atTop (𝓝 (F ((ρu - ρl) • 1))) := by
  let f := fun k (x : ℕ → Fin q → ℝ) => F (cavityWindowGram
    (cavityNormalizeFrame (cavityGaussianMatrix x (N k))) (l k) (u k))
  have hfm (k : ℕ) : Measurable (f k) :=
    (F.continuous.comp (continuous_cavityWindowGram (N k) q (l k) (u k))).measurable.comp
      (measurable_cavityGaussianNormalizedFrame q (N k))
  have hfi (k : ℕ) : Integrable (f k) (cavityGaussianRows q) := by
    apply Integrable.of_bound (hfm k).aestronglyMeasurable ‖F‖
    exact ae_of_all _ (fun x => F.norm_coe_le_norm _)
  have hb (k : ℕ) (x : ℕ → Fin q → ℝ) : |f k x| ≤ ‖F‖ :=
    F.norm_coe_le_norm _
  have hlim := cavityWindowGram_tendsto_ae q N l u hN hu hl hle hue ρl ρu hρl hρu
  have hfu : Tendsto (fun k => ∫ x, f k x ∂cavityGaussianRows q) atTop
      (𝓝 (F ((ρu - ρl) • 1))) := by
    have ht := tendsto_integral_of_dominated_convergence (fun _ : ℕ → Fin q → ℝ => ‖F‖)
      (fun k => (hfm k).aestronglyMeasurable) (integrable_const _)
      (fun k => ae_of_all _ (fun x => F.norm_coe_le_norm _))
      (hlim.mono (fun x hx => F.continuous.continuousAt.tendsto.comp hx))
    simpa only [integral_const, probReal_univ, one_smul] using ht
  have hdiff := cavity_conditioning_tendsto (cavityGaussianRows q)
    (fun k => cavityGoodGram q (N k)) (fun k => measurableSet_cavityGoodGram q (N k))
    ((cavityGoodGram_probability_tendsto q).comp hN) f hfi ‖F‖ hb
  have hcond : Tendsto (fun k => ∫ x, f k x
      ∂cond (cavityGaussianRows q) (cavityGoodGram q (N k))) atTop
      (𝓝 (F ((ρu - ρl) • 1))) := by
    convert hdiff.add hfu using 1 <;> simp
  apply hcond.congr'
  filter_upwards [hN.eventually (cavityGoodGram_eventually_positive q)] with k hk
  exact cavityFrame_integral_eq_haar hk (μ k) (A₀ k) (hA₀ k)
    (fun A => F (cavityWindowGram A (l k) (u k)))
    (F.continuous.comp (continuous_cavityWindowGram (N k) q (l k) (u k)))

end InvariantIsing

end

end OAI
