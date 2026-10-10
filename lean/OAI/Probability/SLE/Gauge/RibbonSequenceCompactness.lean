import OAI.Probability.SLE.Geometry.ActualGuideCompactness
import OAI.Probability.SLE.Gauge.RibbonCoordinateLimit

namespace OAI

/-! Joint extraction of normalized Loewner charts, physical and parameter
guides, and local ribbon coordinate maps under a raw waypoint-angle bound. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace SLEExactGauge

private theorem uniform_subsequence {X Y : Type*} [UniformSpace Y]
    {f : ℕ → X → Y} {g : X → Y} {S : Set X}
    (h : TendstoUniformlyOn f g atTop S) {ψ : ℕ → ℕ} (hψ : StrictMono ψ) :
    TendstoUniformlyOn (fun n => f (ψ n)) g atTop S := by
  intro u hu
  exact hψ.tendsto_atTop.eventually (h u hu)

private theorem locally_uniform_subsequence {X Y : Type*} [TopologicalSpace X] [UniformSpace Y]
    {f : ℕ → X → Y} {g : X → Y} {S : Set X}
    (h : TendstoLocallyUniformlyOn f g atTop S) {ψ : ℕ → ℕ} (hψ : StrictMono ψ) :
    TendstoLocallyUniformlyOn (fun n => f (ψ n)) g atTop S := by
  intro u hu x hx
  obtain ⟨V, hV, he⟩ := h u hu x hx
  exact ⟨V, hV, hψ.tendsto_atTop.eventually he⟩

/-- The physical guide in the joint limit is the guide drawn in the
limiting coordinate chart. This uses uniform chart convergence, rather
than assuming the guide identity survives moving evaluation points. -/
theorem coordinate_guide_limit_identity
    (Qₙ : ℕ → ℂ → ℂ) (Q : ℂ → ℂ) (K : Set ℂ) (hK : IsClosed K)
    (hQ : ContinuousOn Q K) (hQconv : TendstoUniformlyOn Qₙ Q atTop K)
    (xₙ : ℕ → ℝ) (x : ℝ) (hx : Tendsto xₙ atTop (𝓝 x))
    (αₙ : ℕ → ℝ → ℂ) (α : ℝ → ℂ)
    (hαconv : TendstoUniformlyOn αₙ α atTop (Icc 0 2))
    (hmem : ∀ n t, t ∈ Icc (0 : ℝ) 2 →
      RibbonCoordinates.guideCoordinate 0 (xₙ n) t ∈ K)
    (hshape : ∀ n t, t ∈ Icc (0 : ℝ) 2 →
      αₙ n t = Qₙ n (RibbonCoordinates.guideCoordinate 0 (xₙ n) t)) :
    EqOn α (fun t => Q (RibbonCoordinates.guideCoordinate 0 x t)) (Icc 0 2) := by
  intro t ht
  have hqc : Continuous (fun y : ℝ => RibbonCoordinates.guideCoordinate 0 y t) := by
    unfold RibbonCoordinates.guideCoordinate
    fun_prop
  have hqt := (hqc.tendsto x).comp hx
  have hqK : RibbonCoordinates.guideCoordinate 0 x t ∈ K :=
    hK.mem_of_tendsto hqt (Eventually.of_forall (fun n => hmem n t ht))
  have hqwithin : Tendsto (fun n => RibbonCoordinates.guideCoordinate 0 (xₙ n) t)
      atTop (𝓝[K] (RibbonCoordinates.guideCoordinate 0 x t)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hqt, Eventually.of_forall (fun n => hmem n t ht)⟩
  have hlim := hQconv.tendsto_comp (hQ _ hqK) hqwithin
  have halim : Tendsto (fun n => αₙ n t) atTop
      (𝓝 (Q (RibbonCoordinates.guideCoordinate 0 x t))) := by
    convert hlim using 1
    funext n
    exact hshape n t ht
  exact tendsto_nhds_unique (hαconv.tendsto_at ht) halim

/-- The normalized Loewner charts and coordinate charts admit one common
subsequence under the raw waypoint-angle normalization hypothesis. -/
theorem actual_ribbon_joint_compactness
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (hcompact : PublishedHalfPlaneUnivalentCompactness)
    (hboundary : PublishedLoewnerBoundaryExtension)
    (U : ℕ → ℝ≥0 → ℝ) (γₙ : ℕ → ℝ≥0 → ℂ)
    (G F₀ : ℕ → ℝ≥0 → ℂ → ℂ)
    (hU : ∀ n, Continuous (U n))
    (hw : ∀ n, IsCapacityTwoWitness (U n) (γₙ n) (G n) (F₀ n))
    (T : ℕ → ℝ≥0) (hT : ∀ n, 0 < T n)
    (hfresh : ∀ n s, s < T n → γₙ n (T n) ∈ survivingDomain (γₙ n) s)
    (αₙ : ℕ → ℝ → ℂ) (C : ℝ≥0) (s c A : ℝ)
    (hC : 0 < (C : ℝ)) (hs : 0 < s) (hc : 0 < c)
    (hαL : ∀ n, LipschitzOnWith C (αₙ n) (Icc 0 2))
    (hα0 : ∀ n, αₙ n 0 = γₙ n (T n)) (haBound : ∀ n, ‖γₙ n (T n)‖ ≤ A)
    (hchord : ∀ n u, u ∈ Icc (0 : ℝ) 2 → ∀ v, v ∈ Icc (0 : ℝ) 2 →
      c * |u - v| ≤ dist (αₙ n u) (αₙ n v))
    (hαD : ∀ n, MapsTo (αₙ n) (Ioc 0 2) (survivingDomain (γₙ n) (T n)))
    (hclear : ∀ δ : ℝ, 0 < δ → δ ≤ 2 → ∃ r : ℝ, 0 < r ∧
      ∀ n t, t ∈ Icc δ 2 → ball (αₙ n t) r ⊆ survivingDomain (γₙ n) (T n))
    (Qₙ : ℕ → ℂ → ℂ) (K : Set ℂ) (hK : IsCompact K)
    (x₀ : ℂ) (hx₀ : x₀ ∈ K) (Cq Lq : ℝ≥0) (Rq : ℝ)
    (hQupper : ∀ n, LipschitzOnWith Cq (Qₙ n) K)
    (hQlower : ∀ n x, x ∈ K → ∀ y, y ∈ K → dist x y ≤ Lq * dist (Qₙ n x) (Qₙ n y))
    (hQtip : ∀ n, ‖Qₙ n x₀‖ ≤ Rq)
    (hQheight : ∀ n z, z ∈ K → 0 ≤ (Qₙ n z).im)
    (hplanar : PublishedPlanarDiskOpenness)
    (hangle : ∀ n, s ≤ (G n (T n) (αₙ n (1 / 2)) - (U n (T n) : ℂ)).im /
      ‖G n (T n) (αₙ n (1 / 2)) - (U n (T n) : ℂ)‖) :
    ∃ (Q : ℂ → ℂ) (b : ℕ → ℝ) (Fb : ℕ → ℂ → OnePoint ℂ) (βₙ : ℕ → ℝ → ℂ)
      (φ : ℕ → ℕ) (F : ℂ → ℂ) (α β : ℝ → ℂ),
      (∀ n, 0 < b n) ∧
      (∀ n, ContinuousOn (Fb n) {z : ℂ | 0 ≤ z.im}) ∧
      (∀ n z, z ∈ upperHalfPlane → Fb n z =
        (normalizedInverse (F₀ n (T n)) (U n (T n)) (b n) z : OnePoint ℂ)) ∧
      (∀ n, ContinuousOn (βₙ n) (Icc 0 2)) ∧
      (∀ n, βₙ n 0 = 0) ∧
      (∀ n t, t ∈ Icc (0 : ℝ) 2 → 0 ≤ (βₙ n t).im) ∧
      (∀ n t, t ∈ Ioc (0 : ℝ) 2 → βₙ n t =
        normalizedForward (G n (T n)) (U n (T n)) (b n) (αₙ n t)) ∧
      (∀ n t, t ∈ Icc (0 : ℝ) 2 → Fb n (βₙ n t) = (αₙ n t : OnePoint ℂ)) ∧
      StrictMono φ ∧ DifferentiableOn ℂ F upperHalfPlane ∧ InjOn F upperHalfPlane ∧
      (∀ z ∈ upperHalfPlane, deriv F z ≠ 0) ∧ α 0 ∉ F '' upperHalfPlane ∧
      TendstoLocallyUniformlyOn
        (fun n => normalizedInverse (F₀ (φ n) (T (φ n))) (U (φ n) (T (φ n))) (b (φ n)))
        F atTop upperHalfPlane ∧
      TendstoUniformlyOn (fun n => αₙ (φ n)) α atTop (Icc 0 2) ∧
      TendstoUniformlyOn (fun n => βₙ (φ n)) β atTop (Icc 0 2) ∧
      Tendsto (fun n => γₙ (φ n) (T (φ n))) atTop (𝓝 (α 0)) ∧
      LipschitzOnWith C α (Icc 0 2) ∧ ContinuousOn α (Icc 0 2) ∧ InjOn α (Icc 0 2) ∧
      β 0 = 0 ∧ ContinuousOn β (Icc 0 2) ∧ InjOn β (Icc 0 2) ∧
      MapsTo β (Ioc 0 2) upperHalfPlane ∧ EqOn (F ∘ β) α (Ioc 0 2) ∧
      TendstoUniformlyOn (fun n => Qₙ (φ n)) Q atTop K ∧
      LipschitzOnWith Cq Q K ∧
      (∀ x ∈ K, ∀ y ∈ K, dist x y ≤ Lq * dist (Q x) (Q y)) ∧
      InjOn Q K ∧ MapsTo Q (interior K) upperHalfPlane := by
  obtain ⟨b, Fb, βₙ, φ, F, α, β, hb, hbar, hext, hβc, hβ0, hβH, hβeq,
      hbarα, hφ, hF, hiF, hFne, homitlim, hFconv, hαconv, hβconv, hatip,
      hαLlim, hαclim, hαilim, hβlim0, hβlimc, hβlimi, hβlimH, hlimrel⟩ :=
    actual_guide_joint_compactness_with_family P κ hκ hκ8 γ hSLE hcompact hboundary
      U γₙ G F₀ hU hw T hT hfresh αₙ C s c A hC hs hc hαL hα0 haBound hchord hαD hclear hangle
  obtain ⟨Q, ψ, hψ, hQconv, hQu, hQl, hQi, hQH⟩ :=
    RibbonCoordinates.exists_bilip_halfPlane_subsequence hplanar (fun n => Qₙ (φ n))
      K hK x₀ hx₀ Cq Lq Rq (fun n => hQupper (φ n)) (fun n => hQlower (φ n))
      (fun n => hQtip (φ n)) (fun n => hQheight (φ n))
  have hFsub := locally_uniform_subsequence hFconv hψ
  have hαsub := uniform_subsequence hαconv hψ
  have hβsub := uniform_subsequence hβconv hψ
  exact ⟨Q, b, Fb, βₙ, φ ∘ ψ, F, α, β, hb, hbar, hext, hβc, hβ0, hβH,
    hβeq, hbarα, hφ.comp hψ, hF, hiF, hFne, homitlim, hFsub, hαsub, hβsub,
    hatip.comp hψ.tendsto_atTop, hαLlim, hαclim, hαilim, hβlim0, hβlimc, hβlimi,
    hβlimH, hlimrel, hQconv, hQu, hQl, hQi, hQH⟩

end SLEExactGauge

end

end OAI
