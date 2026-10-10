import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Transfer.AssembledRealTransfer

namespace OAI

/-!
# Data retained from one actual real finite transfer

This record keeps the geometric and analytic outputs needed by the
countable model sequence. Its existence is proved by the assembled
construction, with the same explicit published inputs.
-/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

structure RealTransferStage {S : Type*} {n : ℕ}
    (G : Set Sphere) (π : Sphere → Sphere) (σ : S → Sphere)
    (u : Fin n → (ℝ × ℝ) → ℝ) (a b : Fin n → S → ℝ)
    (Flag : Set S) (O : S → Set Sphere) (K₀ : Set (ℝ × ℝ)) (ε : ℝ) where
  indices : Set S
  finite_indices : indices.Finite
  flags : Flag ⊆ indices
  terminals : PhysicalTerminalDisks G π (π '' Gᶜ) (fun s : indices => σ s) (fun s => O s)
  core : Set (ℝ × ℝ)
  core_closed : IsClosed core
  core_contains : K₀ ⊆ interior core
  core_source : core ⊆ realChartDomain G
  core_cocompact : IsCompact (closure coreᶜ)
  core_model : sphericalCore core ⊆ openCompletedRegion terminals.H
  functions : Fin n → (ℝ × ℝ) → ℝ
  extension : Set (ℝ × ℝ)
  extension_open : IsOpen extension
  extension_contains : realChartDomain (completedRegion terminals.H) ⊆ extension
  functions_smooth : ∀ l, ContDiffOn ℝ ∞ (functions l) extension
  retained : ∀ᶠ z in 𝓝ˢ core, ∀ l, functions l z = u l z
  radius : ℝ
  radius_pos : 0 < radius
  metric : (ℝ × ℝ) → PlanarMetric
  metric_smooth : ContDiff ℝ ∞ metric
  metric_pos : ∀ z, (metric z).PosDef
  metric_core : ∀ᶠ z in 𝓝ˢ core, metric z = sphericalMetricFactor z • 1
  metric_far : ∀ z ∉ Metric.closedBall 0 radius, metric z = sphericalMetricFactor z • 1
  source_energy : ∀ l (E : Set (ℝ × ℝ)), MeasurableSet E → E ⊆ core →
    (∫ z in realChartDomain (completedRegion terminals.H) \ E, gradientEnergy (functions l) metric z) <
      (∫ z in realChartDomain G \ E,
        gradientEnergy (u l) (fun z => sphericalMetricFactor z • 1) z) + ε
  excess : ∀ l, Real.sqrt (∑' s : indices,
    max (terminalOscillation (terminals.H s) (functions l) - (b l s - a l s)) 0 ^ 2) < ε
  oscillation : ∀ l, Real.sqrt (∑' s : indices, terminalOscillation (terminals.H s) (functions l) ^ 2) <
    Real.sqrt (∑' s : S, (b l s - a l s) ^ 2) + ε
  domain : Set Sphere
  forward : Sphere → Sphere
  inverse : Sphere → Sphere
  circle_domain : IsCircleDomain domain
  equivalence : IsSmoothSphereEquivalence forward inverse (openCompletedRegion terminals.H) domain
  conformal_core : IsConformalOn forward (sphericalCore core)
  principal : IsPrincipalNormalized forward
  metric_conformal : ∀ p ∈ openCompletedRegion terminals.H, IsMetricConformalAt metric forward p
  integrable : ∀ l, IntegrableOn (gradientEnergy (functions l) metric)
    (realChartDomain (completedRegion terminals.H))
  transported_smooth : ∀ l, ContDiffOn ℝ ∞ (functions l ∘ sphereRealMap inverse) (realChartDomain domain)

theorem exists_real_transfer_stage
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    {G : Set Sphere} (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hTD : IsTotallyDisconnected (π '' Gᶜ))
    {K₀ : Set (ℝ × ℝ)} (hK₀ : IsClosed K₀) (hK₀G : K₀ ⊆ realChartDomain G)
    {n : ℕ} (hn : 0 < n) (u : Fin n → (ℝ × ℝ) → ℝ)
    (huM : ∀ l, Measurable (u l))
    (hu : ∀ l, ContDiffOn ℝ ∞ (u l) (realChartDomain G))
    (hu2 : ∀ l, MemLp (planarGradient (u l)) 2 (volume.restrict (realChartDomain G)))
    {S : Type*} [Countable S] (σ : S → Sphere) (hσ : Injective σ)
    (hσB : ∀ s, σ s ∈ π '' Gᶜ)
    (U : Set Sphere) (hU : IsOpen U) (f : Fin n → Sphere → ℝ)
    (hf : ∀ l, ContinuousOn (f l) U) (M : Fin n → ℝ)
    (hbounded : ∀ l x, x ∈ U → |f l x| ≤ M l)
    (hphysical : ∀ z : ℂ, (z : Sphere) ∈ G → π (z : Sphere) ∈ U)
    (hpull : ∀ l (z : ℂ), (z : Sphere) ∈ G → u l (Complex.equivRealProdCLM z) = f l (π z))
    (hσU : ∀ s, σ s ∈ closure U)
    (a b : Fin n → S → ℝ) (hwidth : ∀ l s, 0 ≤ b l s - a l s)
    (hwidth2 : ∀ l, Summable (fun s => (b l s - a l s) ^ 2))
    (hband : ∀ l s, {t : ℝ | (σ s, t) ∈ intervalFiberHull (clusterGraph U (f l))} =
      Icc (a l s) (b l s))
    (Flag : Set S) (hFlag : Flag.Finite)
    (hfree : ∀ x ∈ π '' Gᶜ, x ∉ range σ → ∀ l,
      ∃ v : ℝ, {t : ℝ | (x, t) ∈ intervalFiberHull (clusterGraph U (f l))} = {v})
    (hcompat : ∀ (j : Fin n) (d : ℕ) (labels : Fin d → Fin n),
      (∀ i, (labels i).val < j.val) →
      (volume.prod (Measure.pi (fun _ : Fin d => (volume : Measure UnitAddCircle))))
        (freeComponentFailure ((π '' Gᶜ) \ range σ) (circleBandGraph U (f j))
          (fun i => circleBandGraph U (f i)) labels) = 0)
    (O : S → Set Sphere) (hO : ∀ s, O s ∈ 𝓝 (σ s))
    {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) (k₀ : ℕ) :
    Nonempty (RealTransferStage G π σ u a b Flag O K₀ ε) := by
  obtain ⟨N, θ, hA, K, χ, D, m, H, k, F, R, g, V, φ, φi,
      _, _, hK, hK₀K, hKG, hKc, hKQ, hF, hretain, hR, hg, hPD, hcore, hfar,
      henergy, hexcess, hosc, hV, heq, hconf, hnorm, hmetric, hint, htarget, hQΩ⟩ :=
    exists_assembled_real_transfer hsard hsch hcompact hfinite hG hinf π hπ hclosed hsurj
      hr hTD hK₀ hK₀G hn u huM hu hu2 σ hσ hσB U hU f hf M hbounded hphysical hpull
      hσU a b hwidth hwidth2 hband Flag hFlag hfree hcompat O hO hε hρ k₀
  exact ⟨{
    indices := gridTerminalIndices Flag (reciprocalGridStep N) upperPair a b θ
    finite_indices := hA
    flags := fun _ hs => Or.inl hs
    terminals := D
    core := K
    core_closed := hK
    core_contains := hK₀K
    core_source := hKG
    core_cocompact := hKc
    core_model := hKQ
    functions := F
    extension := realChartDomain G ∪ ⋃ j, realJordanInterior (H j)
    extension_open := (isOpen_realChartDomain hG).union
      (isOpen_iUnion fun j => (realJordanInterior_geometry (H j)).1)
    extension_contains := hQΩ
    functions_smooth := hF.1
    retained := hretain
    radius := R
    radius_pos := hR
    metric := g
    metric_smooth := hg
    metric_pos := hPD
    metric_core := hcore
    metric_far := hfar
    source_energy := henergy
    excess := hexcess
    oscillation := hosc
    domain := V
    forward := φ
    inverse := φi
    circle_domain := hV
    equivalence := heq
    conformal_core := hconf
    principal := hnorm
    metric_conformal := hmetric
    integrable := hint
    transported_smooth := htarget }⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
