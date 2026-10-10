import OAI.Geometry.RCD.Sobolev.PositiveSourceGradient

namespace OAI

/-!
# Positive measure sources and bounded Dirichlet tests

Bounded clipping of the Lipschitz core converges in L2 with uniformly bounded
Sobolev norm. Weak energy convergence therefore extends a source mass bound
to every bounded nonnegative Dirichlet test. This argument needs no values of
an arbitrary Sobolev representative on a singular source measure.
-/

open Set MeasureTheory Filter
open scoped InnerProductSpace ENNReal Topology NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Extend a bound on bounded Lipschitz core tests by weak Sobolev convergence. -/
theorem bounded_dirichlet_test_bound_of_core (Ω : Set X) (H : SobolevSpace μ hQ)
    (P : ℝ)
    (hcore : ∀ (ψ : SobolevSpace μ hQ) (v : X → ℝ) (C : ℝ≥0),
      LipschitzWith C v → HasCompactSupport v → tsupport v ⊆ Ω →
      SobolevSpace.toLp μ hQ ψ =ᵐ[μ] v →
      ∀ s : ℝ, 0 ≤ s → (∀ x, 0 ≤ v x ∧ v x ≤ s) →
      energyForm μ hQ H ψ ≤ P * s)
    (φ : SobolevSpace.dirichlet μ hQ Ω) {s : ℝ} (hs : 0 ≤ s)
    (hφ : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ φ.val x ∧
      SobolevSpace.toLp μ hQ φ.val x ≤ s) :
    energyForm μ hQ H φ.val ≤ P * s := by
  obtain ⟨fs, hfs, hlim⟩ := mem_closure_iff_seq_limit.mp φ.property
  obtain ⟨D, hD⟩ := (Metric.isBounded_range_of_tendsto fs hlim).exists_norm_le
  let T := fun i => positiveTruncation μ hQ (fs i) s hs
  have hTb (i : ℕ) : ‖T i‖ ≤ D :=
    (SobolevSpace.norm_compContraction_le μ hQ (positiveClip_lipschitz s)
      (positiveClip_zero hs) (fs i)).trans (hD (fs i) (mem_range_self i))
  have hclip : (positiveClip_lipschitz s).compLp (positiveClip_zero hs)
      (SobolevSpace.toLp μ hQ φ.val) = SobolevSpace.toLp μ hQ φ.val := by
    apply Lp.ext
    filter_upwards [(positiveClip_lipschitz s).coeFn_compLp (positiveClip_zero hs)
      (SobolevSpace.toLp μ hQ φ.val), hφ] with x hx hb
    rw [hx]
    change min (max (SobolevSpace.toLp μ hQ φ.val x) 0) s = _
    rw [max_eq_left hb.1, min_eq_left hb.2]
  have hTl : Tendsto (fun i => SobolevSpace.toLp μ hQ (T i)) atTop
      (𝓝 (SobolevSpace.toLp μ hQ φ.val)) := by
    have ht := ((positiveClip_lipschitz s).continuous_compLp
      (positiveClip_zero hs)).continuousAt.tendsto.comp
      ((SobolevSpace.toLpCLM μ hQ).continuous.continuousAt.tendsto.comp hlim)
    change Tendsto (fun i => (positiveClip_lipschitz s).compLp (positiveClip_zero hs)
      (SobolevSpace.toLp μ hQ (fs i))) atTop
      (𝓝 ((positiveClip_lipschitz s).compLp (positiveClip_zero hs)
        (SobolevSpace.toLp μ hQ φ.val))) at ht
    rw [hclip] at ht
    exact ht
  have hE := SobolevSpace.energyForm_tendsto_of_toLp_tendsto_bounded μ hQ hTb hTl H
  rw [energyForm_comm μ hQ H φ.val]
  apply le_of_tendsto hE
  apply Filter.Eventually.of_forall
  intro i
  rw [energyForm_comm μ hQ (T i) H]
  obtain ⟨v, C, hv, hvc, hvΩ, hfv⟩ := hfs i
  have hTv : SobolevSpace.toLp μ hQ (T i) =ᵐ[μ] positiveClip s ∘ v :=
    (positiveTruncation_coe μ hQ (fs i) hs).trans (hfv.fun_comp (positiveClip s))
  apply hcore (T i) (positiveClip s ∘ v) C
  · simpa only [one_mul] using (positiveClip_lipschitz s).comp hv
  · exact hvc.comp_left (positiveClip_zero hs)
  · exact (tsupport_comp_subset (positiveClip_zero hs) v).trans hvΩ
  · exact hTv
  · exact hs
  · intro x
    exact ⟨le_min (le_max_right _ _) hs, min_le_right _ _⟩

/-- The distributional positive source on the Dirichlet Lipschitz core.
The source is integrated only on continuous representatives. -/
def IsDirichletMeasureSource (Ω : Set X) (H : SobolevSpace μ hQ)
    (σ : Measure X) : Prop :=
  ∀ (ψ : SobolevSpace μ hQ) (v : X → ℝ) (C : ℝ≥0),
    LipschitzWith C v → HasCompactSupport v → tsupport v ⊆ Ω →
    SobolevSpace.toLp μ hQ ψ =ᵐ[μ] v →
    energyForm μ hQ H ψ = ∫ x, v x ∂σ

variable [BorelSpace X]

/-- A finite positive source controls every bounded nonnegative Dirichlet
energy test by its mass on the domain. -/
theorem IsDirichletMeasureSource.bounded_test_bound (Ω : Set X)
    (H : SobolevSpace μ hQ) (σ : Measure X) [IsFiniteMeasure σ]
    (hΩ : MeasurableSet Ω) (hsource : IsDirichletMeasureSource μ hQ Ω H σ)
    (φ : SobolevSpace.dirichlet μ hQ Ω) {s : ℝ} (hs : 0 ≤ s)
    (hφ : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ φ.val x ∧
      SobolevSpace.toLp μ hQ φ.val x ≤ s) :
    energyForm μ hQ H φ.val ≤ σ.real Ω * s := by
  apply bounded_dirichlet_test_bound_of_core μ hQ Ω H (σ.real Ω) _ φ hs hφ
  intro ψ v C hv hvc hvΩ hψ t ht hvt
  rw [hsource ψ v C hv hvc hvΩ hψ]
  have hvi : Integrable v σ := by
    apply (integrable_const t).mono' hv.continuous.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hvt x).1]
      exact (hvt x).2
  have hbound : v ≤ᵐ[σ] Ω.indicator (fun _ => t) := by
    apply Filter.Eventually.of_forall
    intro x
    by_cases hx : x ∈ Ω
    · simpa only [indicator_of_mem hx] using (hvt x).2
    · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport
        (fun hm => hx (hvΩ hm))]
  calc
    _ ≤ ∫ x, Ω.indicator (fun _ => t) x ∂σ :=
      integral_mono_ae hvi ((integrable_const t).indicator hΩ) hbound
    _ = σ.real Ω * t := by rw [integral_indicator hΩ, setIntegral_const, smul_eq_mul]

variable [ProperSpace X]

/-- The manuscript's positive-source bounds from a positive measure identity
on compact Lipschitz tests. Singular source mass is retained. -/
theorem positive_source_bounds_of_measure (Ω : Set X) (hΩ : MeasurableSet Ω)
    (hΩfin : μ Ω ≠ ∞) (H : SobolevSpace.dirichlet μ hQ Ω)
    (σ : Measure X) [IsFiniteMeasure σ]
    (hsource : IsDirichletMeasureSource μ hQ Ω H.val σ)
    {d C B : ℝ} (hd : 1 < d) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hH : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ H.val x ∧
      SobolevSpace.toLp μ hQ H.val x ≤ B)
    (hsob : ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      (∫ x in Ω, |SobolevSpace.toLp μ hQ φ.val x| ^ (2 * d) ∂μ) ^ (1 / d) ≤
        C * energyForm μ hQ φ.val φ.val) :
    IntegrableOn (fun x => SobolevSpace.minimalSlope μ hQ H.val x) Ω μ ∧
      (∫ x in Ω, SobolevSpace.minimalSlope μ hQ H.val x ∂μ) ≤
        σ.real Ω * positiveSourceGradientBound (μ.real Ω) C d ((1 + d) / 2) ∧
      (∫ x, (SobolevSpace.minimalSlope μ hQ H.val x) ^ 2 ∂μ) ≤ σ.real Ω * B := by
  apply positive_source_bounds μ hQ Ω hΩfin H hd hC (measureReal_nonneg) hB hH hsob
  intro φ s hs hφ
  exact hsource.bounded_test_bound μ hQ Ω H.val σ hΩ φ hs hφ

end RegularPointCoordinates

end

end OAI
