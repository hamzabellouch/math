import OAI.Geometry.RCD.Sobolev.BochnerCutoffIdentity
import OAI.Geometry.RCD.Heat.HeatGramEvolution

namespace OAI

/-!
# The actual harmonic heat Gram and its canonical signed source

The local Bochner input, a cutoff with a weak Laplacian, and the published
continuous heat kernel now give the heat Gram evolution. The source is
constructed, with its full singular part and compact support retained.
-/

open Set Metric MeasureTheory
open scoped NNReal InnerProductSpace BoundedContinuousFunction

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {U : E →L[ℝ] SobolevSpace μ hQ} {M : PositiveBilinearMeasure X E}
  {κ : ℝ} {p : X} {r : ℝ} {L : ℝ≥0} {v : E}

namespace LocalHarmonicEnergy

/-- The actual bounded Sobolev product representing the cutoff energy. -/
def cutoffEnergy (G : LocalHarmonicEnergy μ hQ U M κ p r L v)
    (χ : X →ᵇ ℝ) (c : SobolevSpace μ hQ) : SobolevSpace μ hQ :=
  SobolevSpace.product μ hQ G.energy c (L ^ 2 * ‖v‖₊ ^ 2) ‖χ‖₊

/-- The canonical full signed source, not a density-only replacement. -/
def cutoffSource (G : LocalHarmonicEnergy μ hQ U M κ p r L v)
    (χ : X →ᵇ ℝ) (c : SobolevSpace μ hQ) (q : Lp ℝ 2 μ) : SignedMeasure X :=
  cutoffMeasureSource μ hQ G.energy c q (harmonicBochnerSource μ hQ U M κ v) χ

omit [ProperSpace X] [FiniteDimensional ℝ E] in
/-- This product has exactly the required cutoff Gram representative. -/
theorem cutoffEnergy_coe (G : LocalHarmonicEnergy μ hQ U M κ p r L v)
    (χ : X →ᵇ ℝ) (hχΩ : tsupport (χ : X → ℝ) ⊆ ball p (2 * r))
    (c : SobolevSpace μ hQ) (hc : SobolevSpace.toLp μ hQ c =ᵐ[μ] χ) :
    SobolevSpace.toLp μ hQ (G.cutoffEnergy μ hQ χ c) =ᵐ[μ]
      fun x => χ x * (SobolevSpace.minimalSlope μ hQ (U v) x) ^ 2 := by
  have hcb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ c x| ≤ (‖χ‖₊ : ℝ) := by
    filter_upwards [hc] with x hx
    simpa only [hx, Real.norm_eq_abs, coe_nnnorm] using χ.norm_coe_le_norm x
  filter_upwards [SobolevSpace.product_coe μ hQ G.energy c _ _ G.bounded hcb,
    hc, (ae_restrict_iff' measurableSet_ball).mp G.representative,
    localGamma_self μ hQ (U v)] with x hx hcx hGx hΓx
  change SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ G.energy c _ _) x = _
  rw [hx, hcx]
  by_cases hin : x ∈ ball p (2 * r)
  · rw [hGx hin, hΓx, mul_comm]
  · have hz : χ x = 0 := by
      by_contra hn
      exact hin (hχΩ (subset_closure hn))
    rw [hz, mul_zero, zero_mul]

omit [FiniteDimensional ℝ E] in
/-- The global measure equation is derived from the local Bochner equation. -/
theorem cutoffEnergy_laplacian (G : LocalHarmonicEnergy μ hQ U M κ p r L v)
    (χ : X →ᵇ ℝ) (hχs : HasCompactSupport (χ : X → ℝ))
    (hχΩ : tsupport (χ : X → ℝ) ⊆ ball p (2 * r))
    (c : SobolevSpace μ hQ) (hc : SobolevSpace.toLp μ hQ c =ᵐ[μ] χ)
    (q : Lp ℝ 2 μ) (hq : IsWeakLaplacian μ hQ c q) :
    IsMeasureLaplacian μ hQ (G.cutoffEnergy μ hQ χ c) (G.cutoffSource μ hQ χ c q) :=
  G.measure_laplacian.cutoff μ hQ χ hχs hχΩ c hc q hq _ G.bounded

variable [μ.Regular] {k : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ k)

/-- Full-source evolution of the actual harmonic heat Gram. Compact
support hypotheses concern only the cutoff and its weak Laplacian. -/
theorem heatGram_hasDerivAt (G : LocalHarmonicEnergy μ hQ U M κ p r L v)
    (χ : X →ᵇ ℝ) (hχs : HasCompactSupport (χ : X → ℝ))
    (hχΩ : tsupport (χ : X → ℝ) ⊆ ball p (2 * r))
    (c : SobolevSpace μ hQ) (hc : SobolevSpace.toLp μ hQ c =ᵐ[μ] χ)
    (q : Lp ℝ 2 μ) (hq : IsWeakLaplacian μ hQ c q)
    (a : X) {R : ℝ} (hR : 0 < R)
    (hχR : ∀ x ∉ closedBall a R, χ x = 0)
    (hqR : ∀ᵐ x ∂μ, x ∉ closedBall a R → q x = 0)
    {t : ℝ} (ht : 0 < t) (x : X) (lambda : ℝ) :
    HasDerivAt (fun s => ⟪v, cutoffHeatGramAt μ hQ hk χ.continuous hχs U s x lambda v⟫_ℝ)
      ((∫ᵛ z, k t x z ∂<•(G.cutoffSource μ hQ χ c q)) + lambda * ‖v‖ ^ 2) t := by
  have hfs := cutoffProduct_zero_off μ hQ G.energy c χ hc _ G.bounded hχR
  have hνs := cutoffMeasureSource_variation_compl μ hQ G.energy c q
    (harmonicBochnerSource μ hQ U M κ v) χ hc measurableSet_closedBall hχR hqR
  apply cutoffHeatGram_hasDerivAt μ hQ hk χ.continuous hχs U v
    (G.cutoffEnergy μ hQ χ c) (G.cutoffEnergy_coe μ hQ χ hχΩ c hc)
    (G.cutoffSource μ hQ χ c q) (G.cutoffEnergy_laplacian μ hQ χ hχs hχΩ c hc q hq)
    a hR _ hνs ht x lambda
  filter_upwards [hfs] with z hz hdist
  exact hz (by simpa only [mem_closedBall, dist_comm, not_le] using hdist)

end LocalHarmonicEnergy
end RegularPointCoordinates

end

end OAI
