import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPolarFixedSection
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPolarFlowTiling

namespace OAI

/-! # Counted polar samplers from the actual inside-letter flow -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric Filter MeasureTheory
open scoped Manifold Pointwise Topology

variable {EG G W EI I A : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  (K : ProperCone ℝ (StrongDual ℝ W))
  [Group I] [TopologicalSpace I] [IsTopologicalGroup I]
  [MeasurableSpace I] [BorelSpace I] [SecondCountableTopology I]
  [NormedAddCommGroup EI] [NormedSpace ℝ EI] [FiniteDimensional ℝ EI]
  [ChartedSpace EI I] [LieGroup (𝓘(ℝ, EI)) ⊤ I] [SimplyConnectedSpace I] [T2Space I]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "C" => heightConePreimage T eW K

/-- A single source partition retains its exact count and all three actual
samplers. The logarithmic chain coordinates are supplied by the proved box
construction, not chosen as additional input. -/
structure PolarTiledSamplerData
    (ExpI : M.coneWordIdeal C → I) (ι : I →* F.N.carrier)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (ε : ℝ) (β : M.ConeIdealBases C) (R : ℝ) (scale : ℕ → ℝ)
    (φ : ℕ → I ≃ₜ* I) where
  tiles : ℕ → ℕ
  anchor : ∀ n, Fin (tiles n) → I
  tile : ∀ n, Fin (tiles n) → Set I
  measurable : ∀ n j, MeasurableSet (tile n j)
  disjoint : ∀ n, Pairwise (fun j l => Disjoint (tile n j) (tile n l))
  cover : ∀ n, (⋃ j, tile n j) = M.coneIdealBox C ExpI
    ((M.supportIn T hunimod eW).weightSupport (normalizedPolarTemplates K ε 0)) β (scale n) 1
  reverse_anchor : ∀ n j, (φ n).symm (anchor n j) ∈ M.coneIdealBox C ExpI
    ((M.supportIn T hunimod eW).weightSupport (normalizedPolarTemplates K ε 1)) β (scale n) 1
  small_tile : ∀ n j, tile n j ⊆ anchor n j • ((φ n) '' M.coneIdealBox C ExpI
    ((M.supportIn T hunimod eW).weightSupport (normalizedPolarTemplates K ε 2)) β (scale n) R)
  count : ∀ n, (tiles n : ℝ) ≤ R ^ finrank ℝ (M.coneWordIdeal C) * Real.exp (scale n *
    ((ε / 3) * ∑ l, M.coneIdealWordCost C (M.polarProbeWidths T hunimod eW K) (β.val l)))
  ambient : M.Bases
  chain : M.TiledProbeChainData T F hunimod eW C ExpI bN
    (normalizedPolarTemplates K ε) (fun _ => β) ambient
    (fun i => ε * M.polarProbeWidths T hunimod eW K i) scale φ ι tiles anchor

omit [SimplyConnectedSpace G] [Nonempty (Fin M.letterCount)]
    [IsTopologicalGroup I] [BorelSpace I] [SecondCountableTopology I]
    [SimplyConnectedSpace I] [T2Space I] in
/-- The largest normalized template is a common reference box for the
three chains. This equality uses its actual polar support widths. -/
theorem PolarTiledSamplerData.largest_width_chains
    (ExpI : M.coneWordIdeal C → I) (ι : I →* F.N.carrier)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {ε : ℝ} (hε : 0 ≤ ε) (β : M.ConeIdealBases C) (R : ℝ) (scale : ℕ → ℝ)
    (φ : ℕ → I ≃ₜ* I)
    (D : M.PolarTiledSamplerData T F hunimod eW K ExpI ι bN ε β R scale φ) :
    Nonempty (∀ k, M.BoxProbeChains T F hunimod eW bN (normalizedPolarTemplates K ε k)
      D.ambient ((M.supportIn T hunimod eW).weightSupport (normalizedPolarTemplates K ε 1))
      scale (fun n => D.chain.probe n k)) := by
  have hw : (M.supportIn T hunimod eW).weightSupport (normalizedPolarTemplates K ε 1) =
      fun i => ε * M.polarProbeWidths T hunimod eW K i := by
    funext i
    exact M.weightSupport_polar_smul T hunimod eW K hε i
  rw [hw]
  exact ⟨fun k => Classical.choice (D.chain.chains k)⟩

/-- The published exponential inputs and the proved inside-letter tiling give
actual counted samplers after deleting a finite initial segment of the scales.
No partition, anchor, chain, or exceptional-scale replacement is assumed. -/
theorem exists_polar_tiled_samplers
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (eI : M.coneWordIdeal C ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EI)) I)
    (ExpI : GroupLieAlgebra (𝓘(ℝ, EI)) I → I) (hExpI : IsGroupExponential ExpI)
    (chartI : GroupLieAlgebra (𝓘(ℝ, EI)) I ≃ₜ I) (hchartI : ∀ v, chartI v = ExpI v)
    (dynkinI : NilpotentDynkinExpansionInput EI I)
    (haarI : NilpotentExponentialHaarInput EI I)
    (ι : I →* F.N.carrier) (hι : Function.Injective ι) (hιm : Measurable ι)
    (hcompat : ∀ v : M.coneWordIdeal C,
      ι (ExpI (eI v)) = F.ExpN (F.N.equiv (v : cartanRootIdeal H)))
    (j : cartanRootIdeal H →ₗ⁅ℝ⁆ A) (ρ : F.N.carrier →* Aˣ) (hρ : Function.Injective ρ)
    (hmatch : ∀ x, ρ (F.ExpN (F.N.equiv x)) = algebraExpUnit (j x))
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (i : Fin M.letterCount) (hi : (M.weight i : H →ₗ[ℝ] ℝ) ∈ C)
    {ε U : ℝ} (hε : 0 < ε) (hU : 0 < U) :
    ∃ (β : M.ConeIdealBases C) (μ : MeasureTheory.Measure I)
      (hbij : Function.Bijective ExpI)
      (bQ : Basis (Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)))
        ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule))
      (lift : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) →
        cartanRootIdeal H) (R δ₀ : ℝ),
      (∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (lift j) = bQ j) ∧
      M.IsMaximizingConeIdealBasis C bI (M.polarProbeWidths T hunimod eW K) β ∧
      μ.IsHaarMeasure ∧ 0 < R ∧ 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (scale : ℕ → ℝ), StrictMono scale → Filter.Tendsto scale Filter.atTop Filter.atTop →
      (∀ n, 0 ≤ scale n) →
      ∀ time η : ℕ → ℝ, Filter.Tendsto η Filter.atTop (nhds 0) →
      (∀ᶠ n in Filter.atTop, |time n| ≤ Real.exp ((U * δ + η n) * scale n)) →
      ∃ n₀ : ℕ,
        let r := fun n => scale (n + n₀)
        let φ := fun n => M.coneIdealLetterAutomorphism C eI ExpI hExpI hbij chartI
          hchartI dynkinI i (time (n + n₀))
        ∃ D : M.PolarTiledSamplerData T F hunimod eW K (ExpI ∘ eI) ι bN ε β R r φ,
          D.chain.bQ = bQ ∧ D.chain.lift = lift := by
  classical
  obtain ⟨β, μ, hbij, R, δ₀, hβ, hμ, hR, hδ₀, ht⟩ :=
    M.exists_polar_flow_tiling T hunimod eW K eI ExpI hExpI chartI hchartI dynkinI haarI
      ι hι (F.ExpN ∘ F.N.equiv) hcompat j ρ hρ hmatch bI i hi
      (by positivity : 0 ≤ ε / 3) (by linarith : ε / 3 < 2 * ε / 3)
      (by linarith : 2 * ε / 3 < ε) hU
  let box := Classical.choice (M.nonempty_polar_tiled_probe_box T F hunimod eW K
    haarN dynkinN (ExpI ∘ eI) ι hιm hcompat bN bI hε β hβ)
  refine ⟨β, μ, hbij, box.bQ, box.lift, R, δ₀, box.lifts, hβ, hμ, hR, hδ₀, ?_⟩
  intro δ hδ hd scale hs hscale hr time η hη htime
  have he := ht δ hδ hd scale hs hscale time η hη htime
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp he
  let r := fun n => scale (n + n₀)
  let φ := fun n => M.coneIdealLetterAutomorphism C eI ExpI hExpI hbij chartI
    hchartI dynkinI i (time (n + n₀))
  have htiles (n : ℕ) := hn₀ (n + n₀) (Nat.le_add_left n₀ n)
  dsimp only at htiles
  choose m anchor tile hc ha hrev hm hdis hcover hsmall hcount using htiles
  have hcover' (n) : (⋃ l, tile n l) = M.coneIdealBox C (ExpI ∘ eI)
      ((M.supportIn T hunimod eW).weightSupport (normalizedPolarTemplates K ε 0)) β (r n) 1 :=
    hcover n
  have hrev' (n) (l) : (φ n).symm (anchor n l) ∈ M.coneIdealBox C (ExpI ∘ eI)
      ((M.supportIn T hunimod eW).weightSupport (normalizedPolarTemplates K ε 1)) β (r n) 1 :=
    hrev n l
  have hsmall' (n) (l) : tile n l ⊆ anchor n l • ((φ n) '' M.coneIdealBox C (ExpI ∘ eI)
      ((M.supportIn T hunimod eW).weightSupport (normalizedPolarTemplates K ε 2)) β (r n) R) :=
    hsmall n l
  obtain ⟨ambient, chain, hchainQ, hchainLift⟩ :=
    M.exists_polar_tiled_probe_chains_from_box T F hunimod eW K
    hExp realize haarN dynkinN (ExpI ∘ eI) ι bN hε β box r
    (fun n => hr (n + n₀)) R hR.le φ
    (fun n => F.ExpN (F.N.equiv (time (n + n₀) • M.letter i))) hc m anchor tile hm hdis
    hcover' hrev' hsmall'
  refine ⟨n₀, {
    tiles := m
    anchor := anchor
    tile := tile
    measurable := hm
    disjoint := hdis
    cover := hcover'
    reverse_anchor := hrev'
    small_tile := hsmall'
    count := ?_
    ambient := ambient
    chain := chain }, hchainQ, hchainLift⟩
  intro n
  have hid : 2 * ε / 3 - ε / 3 = ε / 3 := by ring
  simpa only [hid] using hcount n

end PolycyclicRecognition.CartanWordModel

end

end OAI
