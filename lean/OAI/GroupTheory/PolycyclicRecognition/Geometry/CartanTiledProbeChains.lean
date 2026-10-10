import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTiledProbeBoxes
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoxProbeChains

namespace OAI

/-! # Simultaneous actual chains for the three tiled probe sheets -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric
open scoped Manifold Pointwise

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
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
  (C : Set (H →ₗ[ℝ] ℝ))
  [Group I] [TopologicalSpace I] [IsTopologicalGroup I]
  [MeasurableSpace I] [BorelSpace I] [SecondCountableTopology I]

/-- The joint sampler data, packaged before specializing the templates.
This keeps dependent elimination small at the polar-template application. -/
structure TiledProbeChainData
    (ExpI : M.coneWordIdeal C → I)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Fin 3 → Set W) (β : Fin 3 → M.ConeIdealBases C)
    (ambient : M.Bases) (t : Fin M.letterCount → ℝ) (scale : ℕ → ℝ)
    (φ : ℕ → I ≃ₜ* I) (ι : I →* F.N.carrier)
    (tiles : ℕ → ℕ) (anchor : ∀ n, Fin (tiles n) → I) where
  bQ : Basis (Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)))
    ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)
  lift : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) → cartanRootIdeal H
  index : ∀ n, M.coneIdealBox C ExpI
    ((M.supportIn T hunimod eW).weightSupport (E 0)) (β 0) (scale n) 1 → Fin (tiles n)
  probe : ∀ n, Fin 3 →
    (closedBall (0 : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) → ℝ) 1) ×
      (M.coneIdealBox C ExpI ((M.supportIn T hunimod eW).weightSupport (E 0))
        (β 0) (scale n) 1) → F.N.carrier
  lifts : ∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (lift j) = bQ j
  index_measurable : ∀ n, Measurable (index n)
  probe_measurable : ∀ n j, Measurable (probe n j)
  chains : ∀ j, Nonempty (M.BoxProbeChains T F hunimod eW bN (E j) ambient t scale
    (fun n => probe n j))
  first : ∀ n y, probe n 0 y = ι y.2.val * F.ExpN (F.N.equiv
    (quotientLinearSection (M.coneWordIdeal C) bQ lift (bQ.equivFun.symm y.1.val)))
  second : ∀ n y, probe n 1 y = ι ((φ n).symm (anchor n (index n y.2)))
  third : ∀ n y, probe n 2 y = ι ((φ n).symm ((anchor n (index n y.2))⁻¹ * y.2.val))

/-- The actual strict-width partitions produce all three measurable
generator-chain families. The section and word bases are fixed before the
scale sequence; each chain length and prefix bound is uniform in that sequence. -/
theorem exists_tiled_probe_chains
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (ExpI : M.coneWordIdeal C → I) (ι : I →* F.N.carrier) (hι : Measurable ι)
    (hcompat : ∀ v, ι (ExpI v) = F.ExpN (F.N.equiv (v : cartanRootIdeal H)))
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (E : Fin 3 → Set W) (hE : ∀ j, IsCompact (E j)) (hne : ∀ j, (E j).Nonempty)
    (hs : ∀ j i, 0 ≤ (M.supportIn T hunimod eW).weightSupport (E j) i)
    (hzero : ∀ j i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C →
      (M.supportIn T hunimod eW).weightSupport (E j) i = 0)
    (β : Fin 3 → M.ConeIdealBases C)
    (hβ : ∀ j, M.IsMaximizingConeIdealBasis C bI
      ((M.supportIn T hunimod eW).weightSupport (E j)) (β j))
    (ambient : M.Bases) (t : Fin M.letterCount → ℝ)
    (hdom : ∀ j i, (M.supportIn T hunimod eW).weightSupport (E j) i ≤ t i)
    (hambient : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN)
      (fun w => bracketWordExponent t w) ambient.val)
    (scale : ℕ → ℝ) (hr : ∀ n, 0 ≤ scale n) (R : ℝ) (hR : 0 ≤ R)
    (φ : ℕ → I ≃ₜ* I) (k : ℕ → F.N.carrier)
    (hφ : ∀ n z, ι (φ n z) = k n * ι z * (k n)⁻¹)
    (tiles : ℕ → ℕ) (anchor : ∀ n, Fin (tiles n) → I)
    (tile : ∀ n, Fin (tiles n) → Set I)
    (hm : ∀ n j, MeasurableSet (tile n j))
    (hd : ∀ n, Pairwise (fun j l => Disjoint (tile n j) (tile n l)))
    (hu : ∀ n, (⋃ j, tile n j) = M.coneIdealBox C ExpI
      ((M.supportIn T hunimod eW).weightSupport (E 0)) (β 0) (scale n) 1)
    (ha : ∀ n j, (φ n).symm (anchor n j) ∈ M.coneIdealBox C ExpI
      ((M.supportIn T hunimod eW).weightSupport (E 1)) (β 1) (scale n) 1)
    (ht : ∀ n j, tile n j ⊆ anchor n j • ((φ n) '' M.coneIdealBox C ExpI
      ((M.supportIn T hunimod eW).weightSupport (E 2)) (β 2) (scale n) R)) :
    let U := fun n => M.coneIdealBox C ExpI
      ((M.supportIn T hunimod eW).weightSupport (E 0)) (β 0) (scale n) 1
    let Z := closedBall (0 : Fin (finrank ℝ
      (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) → ℝ) 1
    ∃ (bQ : Basis (Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)))
        ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule))
      (lift : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) →
        cartanRootIdeal H)
      (index : ∀ n, U n → Fin (tiles n)) (probe : ∀ n, Fin 3 → Z × U n → F.N.carrier),
      (∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (lift j) = bQ j) ∧
      (∀ n, Measurable (index n)) ∧ (∀ n j, Measurable (probe n j)) ∧
      (∀ j, Nonempty (M.BoxProbeChains T F hunimod eW bN (E j) ambient t scale
        (fun n => probe n j))) ∧
      (∀ n y, probe n 0 y = ι y.2.val * F.ExpN (F.N.equiv
        (quotientLinearSection (M.coneWordIdeal C) bQ lift (bQ.equivFun.symm y.1.val)))) ∧
      (∀ n y, probe n 1 y = ι ((φ n).symm (anchor n (index n y.2)))) ∧
      ∀ n y, probe n 2 y = ι ((φ n).symm ((anchor n (index n y.2))⁻¹ * y.2.val)) := by
  classical
  dsimp only
  obtain ⟨⟨chartN, hchartN⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  let coordinates := ((bN.map F.N.equiv.toLinearEquiv).equivFun.symm.toContinuousLinearEquiv.toHomeomorph).trans chartN
  let : SecondCountableTopology F.N.carrier := coordinates.symm.secondCountableTopology
  let data := Classical.choice (M.nonempty_tiledProbeBoxData C T hunimod eW
    F.N.equiv F.ExpN F.isExpN chartN hchartN dynkinN ExpI ι hι hcompat
    bN bI E hs hzero β hβ)
  let bQ := data.bQ
  let lift := data.lift
  let γ := data.γ
  let R₀ := data.R₀
  have hlift := data.lifts
  have hR₀ := data.radius_nonneg
  have hγ := data.maximizing
  have hboxes := data.select
  have hex (n : ℕ) := hboxes (scale n) (hr n) R hR
    (φ n) (k n) (hφ n) (tiles n) (anchor n) (tile n) (hm n) (hd n) (hu n) (ha n) (ht n)
  let index (n : ℕ) := Classical.choose (hex n)
  let probe (n : ℕ) := Classical.choose (Classical.choose_spec (hex n))
  have properties (n : ℕ) := Classical.choose_spec (Classical.choose_spec (hex n))
  refine ⟨bQ, lift, index, probe, hlift, fun n => (properties n).1,
    fun n => (properties n).2.1, ?_, fun n => (properties n).2.2.2.1,
    fun n => (properties n).2.2.2.2.1, fun n => (properties n).2.2.2.2.2⟩
  intro j
  have hrad : 0 ≤ (![R₀, 1, R] j) := by
    fin_cases j
    · exact hR₀
    · exact zero_le_one
    · exact hR
  exact M.nonempty_boxProbeChains T F hunimod eW hExp realize haarN dynkinN
    bN (E j) (hE j) (hne j) (![R₀, 1, R] j) hrad (γ j) ambient (hγ j)
    t (hdom j) hambient scale hr (fun n => probe n j) (fun n => (properties n).2.1 j)
    (fun n q => (properties n).2.2.1 j q)

theorem nonempty_tiledProbeChainData
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (ExpI : M.coneWordIdeal C → I) (ι : I →* F.N.carrier) (hι : Measurable ι)
    (hcompat : ∀ v, ι (ExpI v) = F.ExpN (F.N.equiv (v : cartanRootIdeal H)))
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (E : Fin 3 → Set W) (hE : ∀ j, IsCompact (E j)) (hne : ∀ j, (E j).Nonempty)
    (hs : ∀ j i, 0 ≤ (M.supportIn T hunimod eW).weightSupport (E j) i)
    (hzero : ∀ j i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C →
      (M.supportIn T hunimod eW).weightSupport (E j) i = 0)
    (β : Fin 3 → M.ConeIdealBases C)
    (hβ : ∀ j, M.IsMaximizingConeIdealBasis C bI
      ((M.supportIn T hunimod eW).weightSupport (E j)) (β j))
    (ambient : M.Bases) (t : Fin M.letterCount → ℝ)
    (hdom : ∀ j i, (M.supportIn T hunimod eW).weightSupport (E j) i ≤ t i)
    (hambient : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN)
      (fun w => bracketWordExponent t w) ambient.val)
    (scale : ℕ → ℝ) (hr : ∀ n, 0 ≤ scale n) (R : ℝ) (hR : 0 ≤ R)
    (φ : ℕ → I ≃ₜ* I) (k : ℕ → F.N.carrier)
    (hφ : ∀ n z, ι (φ n z) = k n * ι z * (k n)⁻¹)
    (tiles : ℕ → ℕ) (anchor : ∀ n, Fin (tiles n) → I)
    (tile : ∀ n, Fin (tiles n) → Set I)
    (hm : ∀ n j, MeasurableSet (tile n j))
    (hd : ∀ n, Pairwise (fun j l => Disjoint (tile n j) (tile n l)))
    (hu : ∀ n, (⋃ j, tile n j) = M.coneIdealBox C ExpI
      ((M.supportIn T hunimod eW).weightSupport (E 0)) (β 0) (scale n) 1)
    (ha : ∀ n j, (φ n).symm (anchor n j) ∈ M.coneIdealBox C ExpI
      ((M.supportIn T hunimod eW).weightSupport (E 1)) (β 1) (scale n) 1)
    (ht : ∀ n j, tile n j ⊆ anchor n j • ((φ n) '' M.coneIdealBox C ExpI
      ((M.supportIn T hunimod eW).weightSupport (E 2)) (β 2) (scale n) R)) :
    Nonempty (M.TiledProbeChainData T F hunimod eW C ExpI bN E β ambient t scale φ ι tiles anchor) := by
  obtain ⟨bQ, lift, index, probe, hl, hi, hp, hc, hp₀, hp₁, hp₂⟩ :=
    M.exists_tiled_probe_chains T F hunimod eW C hExp realize haarN dynkinN
      ExpI ι hι hcompat bN bI E hE hne hs hzero β hβ ambient t hdom hambient
      scale hr R hR φ k hφ tiles anchor tile hm hd hu ha ht
  exact ⟨⟨bQ, lift, index, probe, hl, hi, hp, hc, hp₀, hp₁, hp₂⟩⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
