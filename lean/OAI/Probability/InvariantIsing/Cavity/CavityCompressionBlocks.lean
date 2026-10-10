import OAI.Probability.InvariantIsing.Cavity.CavityHaarCompression
import OAI.Probability.InvariantIsing.Cavity.CavityMeasurableComplement
import OAI.Probability.InvariantIsing.Cavity.CavitySpecialBlocks

namespace OAI

/-! Joint Haar compression limits for the actual measurable cavity block
construction. Only continuity at the prescribed limiting stack is used;
the completion rule need not be continuous on every frame. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology Matrix MatrixOrder Matrix.Norms.L2Operator
  BoundedContinuousFunction

namespace InvariantIsing

lemma cavityFrame_measurable_integral_eq_haar {n q : ℕ}
    (hp : 0 < (cavityGaussianRows q).real (cavityGoodGram q n))
    (μ : Measure (Orthogonal n)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (A₀ : Matrix (Fin n) (Fin q) ℝ) (hA₀ : A₀.transpose * A₀ = 1)
    (f : Matrix (Fin n) (Fin q) ℝ → ℝ) (hf : Measurable f) :
    (∫ x, f (cavityNormalizeFrame (cavityGaussianMatrix x n))
      ∂cond (cavityGaussianRows q) (cavityGoodGram q n)) =
      ∫ U, f ((U : Matrix (Fin n) (Fin n) ℝ) * A₀) ∂μ := by
  have hp' : stdGaussian (EuclideanSpace ℝ (Fin n × Fin q)) (cavityArrayGood n q) ≠ 0 := by
    rw [cavityArrayGood_probability]
    exact fun h => by simp [Measure.real, h] at hp
  let := cavityConditionedFrameLaw_probability hp'
  have hlaw := cavityFrame_eq_haar_orbit μ (cavityConditionedFrameLaw n q)
    cavityConditionedFrameLaw_rotation (cavityConditionedFrameLaw_orthonormal n q) A₀ hA₀
  rw [← integral_map (measurable_cavityGaussianNormalizedFrame q n).aemeasurable
      hf.aestronglyMeasurable, cavityConditionedFrameLaw_of_rows, hlaw]
  exact integral_map
    ((continuous_cavityFrameAction n q).comp (continuous_id.prodMk continuous_const)).aemeasurable
    hf.aestronglyMeasurable

def cavityReindexedStack {m n d : ℕ} (e : Fin (m * n) ≃ Fin (d + n))
    (M : Fin m → Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin (d + n)) (Fin n) ℝ :=
  fun i j => cavitySpectralStack M (e.symm i) j

lemma measurable_cavityReindexedStack {m n d : ℕ} (e : Fin (m * n) ≃ Fin (d + n)) :
    Measurable (cavityReindexedStack e) := by
  apply Measurable.of_eval_matrix
  intro i j
  change Measurable (fun M : Fin m → Matrix (Fin n) (Fin n) ℝ =>
    CFC.sqrt (M (finProdFinEquiv.symm (e.symm i)).1)
      (finProdFinEquiv.symm (e.symm i)).2 j)
  exact (CFC.measurable_sqrt.comp
    (measurable_pi_apply (finProdFinEquiv.symm (e.symm i)).1)).eval_matrix

def cavityCompressionBlocks {m n d : ℕ} (e : Fin (m * n) ≃ Fin (d + n))
    (D : Matrix (Fin (d + n)) (Fin (d + n)) ℝ)
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ)
    (M : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ :=
  cavitySpecialBlocks D (cavitySelectedComplement B₀ (cavityReindexedStack e M))
    (cavityReindexedStack e M)

lemma measurable_cavityCompressionBlocks {m n d : ℕ} (e : Fin (m * n) ≃ Fin (d + n))
    (D : Matrix (Fin (d + n)) (Fin (d + n)) ℝ)
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ) :
    Measurable (cavityCompressionBlocks e D B₀) := by
  have hE : Measurable (cavityReindexedStack e) := measurable_cavityReindexedStack e
  have hB : Measurable (fun M : Fin m → Matrix (Fin n) (Fin n) ℝ =>
      cavitySelectedComplement B₀ (cavityReindexedStack e M)) :=
    (measurable_cavitySelectedComplement B₀).comp hE
  have h := (continuous_cavitySpecialBlocks (d := d) (n := n) D).measurable.comp
    (hB.prodMk hE)
  unfold cavityCompressionBlocks
  exact h

theorem cavityCompressionBlocks_tendsto {m n d : ℕ} (e : Fin (m * n) ≃ Fin (d + n))
    (D : Matrix (Fin (d + n)) (Fin (d + n)) ℝ)
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ) (hB₀ : B₀.transpose * B₀ = 1)
    (ρ : Fin m → ℝ) (hρ : ∀ a, 0 ≤ ρ a)
    (hEB : (cavityReindexedStack e (fun a => ρ a • 1)).transpose * B₀ = 0)
    (M : ℕ → Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ k a, (M k a).PosSemidef)
    (hlim : ∀ a, Tendsto (fun k => M k a) atTop (𝓝 (ρ a • 1))) :
    Tendsto (fun k => cavityCompressionBlocks e D B₀ (M k)) atTop
      (𝓝 (cavitySpecialBlocks D B₀ (cavityReindexedStack e (fun a => ρ a • 1)))) := by
  have hs := cavitySpectralStack_tendsto M ρ hρ hM hlim
  have he : Tendsto (fun k => cavityReindexedStack e (M k)) atTop
      (𝓝 (cavityReindexedStack e (fun a => ρ a • 1))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    have hh := (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hs (e.symm i)) j)
    simpa only [cavityReindexedStack, cavitySpectralStack,
      cavity_sqrt_scalar_identity _ (hρ _), Matrix.smul_apply, smul_eq_mul] using hh
  have hb := cavitySelectedComplement_tendsto _ _ B₀ hB₀ hEB he
  have ht := (continuous_cavitySpecialBlocks (d := d) (n := n) D).tendsto
    (B₀, cavityReindexedStack e (fun a => ρ a • 1)) |>.comp (hb.prodMk_nhds he)
  simpa only [cavityCompressionBlocks, Function.comp_def] using ht

theorem cavityHaarCompressionBlocks_integral_tendsto {m n d : ℕ}
    (e : Fin (m * n) ≃ Fin (d + n))
    (D : Matrix (Fin (d + n)) (Fin (d + n)) ℝ)
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ) (hB₀ : B₀.transpose * B₀ = 1)
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
    (F : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ →ᵇ ℝ) :
    Tendsto (fun k => ∫ U, F (cavityCompressionBlocks e D B₀
      (fun a => cavityWindowGram
        ((U : Matrix (Fin (N k)) (Fin (N k)) ℝ) * A₀ k) (l a k) (u a k))) ∂μ k)
      atTop (𝓝 (F (cavitySpecialBlocks D B₀
        (cavityReindexedStack e (fun a => (ρu a - ρl a) • 1))))) := by
  let G := fun k (A : Matrix (Fin (N k)) (Fin n) ℝ) =>
    F (cavityCompressionBlocks e D B₀ (fun a => cavityWindowGram A (l a k) (u a k)))
  have hG (k : ℕ) : Measurable (G k) :=
    F.continuous.measurable.comp ((measurable_cavityCompressionBlocks e D B₀).comp
      (measurable_pi_iff.mpr (fun a => (continuous_cavityWindowGram
        (N k) n (l a k) (u a k)).measurable)))
  let f := fun k (x : ℕ → Fin n → ℝ) =>
    G k (cavityNormalizeFrame (cavityGaussianMatrix x (N k)))
  have hfm (k : ℕ) : Measurable (f k) :=
    (hG k).comp (measurable_cavityGaussianNormalizedFrame n (N k))
  have hb (k : ℕ) (x : ℕ → Fin n → ℝ) : |f k x| ≤ ‖F‖ := F.norm_coe_le_norm _
  have hfi (k : ℕ) : Integrable (f k) (cavityGaussianRows n) :=
    Integrable.of_bound (hfm k).aestronglyMeasurable ‖F‖ (ae_of_all _ (hb k))
  have hlim : ∀ᵐ x ∂cavityGaussianRows n, ∀ a,
      Tendsto (fun k => cavityWindowGram
        (cavityNormalizeFrame (cavityGaussianMatrix x (N k))) (l a k) (u a k))
        atTop (𝓝 ((ρu a - ρl a) • (1 : Matrix (Fin n) (Fin n) ℝ))) :=
    ae_all_iff.mpr (fun a => cavityWindowGram_tendsto_ae n N (l a) (u a)
      hN (hu a) (hl a) (hle a) (hue a) (ρl a) (ρu a) (hρl a) (hρu a))
  have hfu : Tendsto (fun k => ∫ x, f k x ∂cavityGaussianRows n) atTop
      (𝓝 (F (cavitySpecialBlocks D B₀
        (cavityReindexedStack e (fun a => (ρu a - ρl a) • 1))))) := by
    have ht := tendsto_integral_of_dominated_convergence (fun _ : ℕ → Fin n → ℝ => ‖F‖)
      (fun k => (hfm k).aestronglyMeasurable) (integrable_const _)
      (fun k => ae_of_all _ (hb k)) (hlim.mono (fun x hx =>
        F.continuous.continuousAt.tendsto.comp (cavityCompressionBlocks_tendsto e D B₀ hB₀
          (fun a => ρu a - ρl a) hρ hEB _
          (fun k a => cavityWindowGram_posSemidef _ _ _ (hlu a k)) hx)))
    simpa only [integral_const, probReal_univ, one_smul] using ht
  have hdiff := cavity_conditioning_tendsto (cavityGaussianRows n)
    (fun k => cavityGoodGram n (N k)) (fun k => measurableSet_cavityGoodGram n (N k))
    ((cavityGoodGram_probability_tendsto n).comp hN) f hfi ‖F‖ hb
  have hcond : Tendsto (fun k => ∫ x, f k x
      ∂cond (cavityGaussianRows n) (cavityGoodGram n (N k))) atTop
      (𝓝 (F (cavitySpecialBlocks D B₀
        (cavityReindexedStack e (fun a => (ρu a - ρl a) • 1))))) := by
    convert hdiff.add hfu using 1 <;> simp
  apply hcond.congr'
  filter_upwards [hN.eventually (cavityGoodGram_eventually_positive n)] with k hk
  exact cavityFrame_measurable_integral_eq_haar hk (μ k) (A₀ k) (hA₀ k) (G k) (hG k)

end InvariantIsing

end

end OAI
