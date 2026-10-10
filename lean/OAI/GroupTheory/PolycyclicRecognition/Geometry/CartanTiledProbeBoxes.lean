import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSectionProbeBox
import OAI.GroupTheory.PolycyclicRecognition.Analysis.TiledProbeSamplers

namespace OAI

/-! # Actual tiled probes in the three Cartan template boxes -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric
open scoped Manifold Pointwise

variable {L W : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {H : LieSubalgebra ℝ L} [H.IsCartanSubalgebra] (M : CartanWordModel H)
  (C : Set (H →ₗ[ℝ] ℝ)) {a : ℕ} (T : TriangularAdjoint L a)
  (hunimod : ∀ x : L, LinearMap.trace ℝ L (ad ℝ L x) = 0)
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  {EN N I : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  [FiniteDimensional ℝ EN] [TopologicalSpace N] [ChartedSpace EN N] [Group N]
  [LieGroup (𝓘(ℝ, EN)) ⊤ N] [T2Space N]
  [MeasurableSpace N] [BorelSpace N] [SecondCountableTopology N]
  [Group I] [TopologicalSpace I] [IsTopologicalGroup I]
  [MeasurableSpace I] [BorelSpace I] [SecondCountableTopology I]

/-- Fixed source box data; packaging it keeps later three-chain applications
small when the ambient algebra is an actual tangent Lie algebra. -/
structure TiledProbeBoxData
    (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
    (ExpN : GroupLieAlgebra (𝓘(ℝ, EN)) N → N)
    (ExpI : M.coneWordIdeal C → I) (ι : I →* N)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Fin 3 → Set W) (β : Fin 3 → M.ConeIdealBases C) where
  bQ : Basis (Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)))
    ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)
  lift : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) →
    cartanRootIdeal H
  γ : Fin 3 → M.Bases
  R₀ : ℝ
  lifts : ∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (lift j) = bQ j
  radius_nonneg : 0 ≤ R₀
  maximizing : ∀ j, IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN)
    (M.boxCost T hunimod eW (E j)) (γ j).val
  select : ∀ r : ℝ, 0 ≤ r → ∀ R : ℝ, 0 ≤ R →
      let U := M.coneIdealBox C ExpI
        ((M.supportIn T hunimod eW).weightSupport (E 0)) (β 0) r 1
      let Banchor := M.coneIdealBox C ExpI
        ((M.supportIn T hunimod eW).weightSupport (E 1)) (β 1) r 1
      let Bsmall := M.coneIdealBox C ExpI
        ((M.supportIn T hunimod eW).weightSupport (E 2)) (β 2) r R
      let Z := closedBall (0 : Fin (finrank ℝ
        (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) → ℝ) 1
      let σ : Z → N := fun q => ExpN (eN
        (quotientLinearSection (M.coneWordIdeal C) bQ lift (bQ.equivFun.symm q.val)))
      ∀ (φ : I ≃ₜ* I) (k : N), (∀ z, ι (φ z) = k * ι z * k⁻¹) →
      ∀ (m : ℕ) (anchor : Fin m → I) (tile : Fin m → Set I),
      (∀ j, MeasurableSet (tile j)) →
      Pairwise (fun j l => Disjoint (tile j) (tile l)) → (⋃ j, tile j) = U →
      (∀ j, φ.symm (anchor j) ∈ Banchor) →
      (∀ j, tile j ⊆ anchor j • (φ '' Bsmall)) →
      ∃ (index : U → Fin m) (probe : Fin 3 → Z × U → N),
        Measurable index ∧ (∀ j, Measurable (probe j)) ∧
        (∀ j y, probe j y ∈ M.groupBox T hunimod eW (ExpN ∘ eN)
          (E j) (γ j) r (![R₀, 1, R] j)) ∧
        (∀ y, probe 0 y = ι y.2.val * σ y.1) ∧
        (∀ y, probe 1 y = ι (φ.symm (anchor (index y.2)))) ∧
        ∀ y, probe 2 y = ι (φ.symm ((anchor (index y.2))⁻¹ * y.2.val))

/-- The ideal-section sampler and both reverse-flow samplers lie in the
three actual ambient word boxes. Their bases and the first radius are
chosen uniformly before the scale, partition and flow. -/
theorem exists_tiled_probe_boxes
    (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
    (ExpN : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExpN : IsGroupExponential ExpN)
    (chartN : GroupLieAlgebra (𝓘(ℝ, EN)) N ≃ₜ N) (hchartN : ∀ v, chartN v = ExpN v)
    (dynkinN : NilpotentDynkinExpansionInput EN N)
    (ExpI : M.coneWordIdeal C → I) (ι : I →* N) (hι : Measurable ι)
    (hcompat : ∀ v, ι (ExpI v) = ExpN (eN (v : cartanRootIdeal H)))
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (E : Fin 3 → Set W)
    (hs : ∀ j i, 0 ≤ (M.supportIn T hunimod eW).weightSupport (E j) i)
    (hzero : ∀ j i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C →
      (M.supportIn T hunimod eW).weightSupport (E j) i = 0)
    (β : Fin 3 → M.ConeIdealBases C)
    (hβ : ∀ j, M.IsMaximizingConeIdealBasis C bI
      ((M.supportIn T hunimod eW).weightSupport (E j)) (β j)) :
    ∃ (bQ : Basis (Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)))
        ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule))
      (lift : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) →
        cartanRootIdeal H) (γ : Fin 3 → M.Bases) (R₀ : ℝ),
      (∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (lift j) = bQ j) ∧ 0 ≤ R₀ ∧
      (∀ j, IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN)
        (M.boxCost T hunimod eW (E j)) (γ j).val) ∧
      ∀ r : ℝ, 0 ≤ r → ∀ R : ℝ, 0 ≤ R →
      let U := M.coneIdealBox C ExpI
        ((M.supportIn T hunimod eW).weightSupport (E 0)) (β 0) r 1
      let Banchor := M.coneIdealBox C ExpI
        ((M.supportIn T hunimod eW).weightSupport (E 1)) (β 1) r 1
      let Bsmall := M.coneIdealBox C ExpI
        ((M.supportIn T hunimod eW).weightSupport (E 2)) (β 2) r R
      let Z := closedBall (0 : Fin (finrank ℝ
        (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) → ℝ) 1
      let σ : Z → N := fun q => ExpN (eN
        (quotientLinearSection (M.coneWordIdeal C) bQ lift (bQ.equivFun.symm q.val)))
      ∀ (φ : I ≃ₜ* I) (k : N), (∀ z, ι (φ z) = k * ι z * k⁻¹) →
      ∀ (m : ℕ) (anchor : Fin m → I) (tile : Fin m → Set I),
      (∀ j, MeasurableSet (tile j)) →
      Pairwise (fun j l => Disjoint (tile j) (tile l)) → (⋃ j, tile j) = U →
      (∀ j, φ.symm (anchor j) ∈ Banchor) →
      (∀ j, tile j ⊆ anchor j • (φ '' Bsmall)) →
      ∃ (index : U → Fin m) (probe : Fin 3 → Z × U → N),
        Measurable index ∧ (∀ j, Measurable (probe j)) ∧
        (∀ j y, probe j y ∈ M.groupBox T hunimod eW (ExpN ∘ eN)
          (E j) (γ j) r (![R₀, 1, R] j)) ∧
        (∀ y, probe 0 y = ι y.2.val * σ y.1) ∧
        (∀ y, probe 1 y = ι (φ.symm (anchor (index y.2)))) ∧
        ∀ y, probe 2 y = ι (φ.symm ((anchor (index y.2))⁻¹ * y.2.val)) := by
  let : IsTopologicalGroup N := topologicalGroup_of_lieGroup (𝓘(ℝ, EN)) ⊤
  obtain ⟨bQ, lift, hlift, γ₀, R₀, hR₀, hγ₀, hfirst⟩ :=
    M.exists_section_probe_box C T hunimod eW eN ExpN hExpN dynkinN
      bN bI (E 0) (hs 0) (hzero 0) (β 0) (hβ 0)
  obtain ⟨γ₁, hγ₁, hanchor⟩ := M.exists_ideal_probe_box C T hunimod eW
    bN bI (E 1) (hs 1) (hzero 1) (β 1) (hβ 1)
  obtain ⟨γ₂, hγ₂, hsmall⟩ := M.exists_ideal_probe_box C T hunimod eW
    bN bI (E 2) (hs 2) (hzero 2) (β 2) (hβ 2)
  refine ⟨bQ, lift, ![γ₀, γ₁, γ₂], R₀, hlift, hR₀, ?_, ?_⟩
  · intro j
    fin_cases j
    · exact hγ₀
    · exact hγ₁
    · exact hγ₂
  intro r hr R hR
  dsimp only
  let U := M.coneIdealBox C ExpI
    ((M.supportIn T hunimod eW).weightSupport (E 0)) (β 0) r 1
  let Banchor := M.coneIdealBox C ExpI
    ((M.supportIn T hunimod eW).weightSupport (E 1)) (β 1) r 1
  let Bsmall := M.coneIdealBox C ExpI
    ((M.supportIn T hunimod eW).weightSupport (E 2)) (β 2) r R
  let Z := closedBall (0 : Fin (finrank ℝ
    (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) → ℝ) 1
  let σ : Z → N := fun q => ExpN (eN
    (quotientLinearSection (M.coneWordIdeal C) bQ lift (bQ.equivFun.symm q.val)))
  have hσ : Measurable σ := by
    let : MeasurableSpace (GroupLieAlgebra (𝓘(ℝ, EN)) N) := borel _
    let : BorelSpace (GroupLieAlgebra (𝓘(ℝ, EN)) N) := ⟨rfl⟩
    let F := eN.toLinearMap.comp ((quotientLinearSection (M.coneWordIdeal C) bQ lift).comp
      bQ.equivFun.symm.toLinearMap)
    have he : σ = fun q : Z => chartN (F q.val) := by
      funext q
      exact (hchartN _).symm
    rw [he]
    exact chartN.continuous.measurable.comp
      (F.continuous_of_finiteDimensional.measurable.comp measurable_subtype_coe)
  intro φ k hφ m anchor tile hm hd hu ha ht
  obtain ⟨index, probe, hi, hp, hp₀, hp₁, hp₂, hpa, hps, _⟩ :=
    exists_measurable_tiled_probe_samplers ι hι φ k hφ σ hσ U Banchor Bsmall
      anchor tile hm hd hu ha ht
  have hincl (j : Fin 3) (radius : ℝ) (hincl :
      M.coneIdealBox C (fun v => ExpN (eN (v : cartanRootIdeal H)))
        ((M.supportIn T hunimod eW).weightSupport (E j)) (β j) r radius ⊆
      M.groupBox T hunimod eW (ExpN ∘ eN) (E j) (![γ₀, γ₁, γ₂] j) r radius)
      {z : I} (hz : z ∈ M.coneIdealBox C ExpI
        ((M.supportIn T hunimod eW).weightSupport (E j)) (β j) r radius) :
      ι z ∈ M.groupBox T hunimod eW (ExpN ∘ eN) (E j) (![γ₀, γ₁, γ₂] j) r radius := by
    obtain ⟨v, hv, hb⟩ := hz
    apply hincl
    exact ⟨v, (hcompat v).symm.trans (congrArg ι hv), hb⟩
  refine ⟨index, probe, hi, hp, ?_, hp₀, hp₁, hp₂⟩
  intro j y
  fin_cases j
  · change probe 0 y ∈ M.groupBox T hunimod eW (ExpN ∘ eN) (E 0) γ₀ r R₀
    rw [hp₀]
    obtain ⟨v, hv, hb⟩ := y.2.property
    rw [← hv, hcompat]
    exact hfirst r hr v (bQ.equivFun.symm y.1.val) hb (by
      rw [LinearEquiv.apply_symm_apply]
      exact mem_closedBall_zero_iff.mp y.1.property)
  · change probe 1 y ∈ M.groupBox T hunimod eW (ExpN ∘ eN) (E 1) γ₁ r 1
    obtain ⟨z, hz, he⟩ := hpa y
    rw [← he]
    exact hincl 1 1 (hanchor (ExpN ∘ eN) r 1 zero_le_one) hz
  · change probe 2 y ∈ M.groupBox T hunimod eW (ExpN ∘ eN) (E 2) γ₂ r R
    obtain ⟨z, hz, he⟩ := hps y
    rw [← he]
    exact hincl 2 R (hsmall (ExpN ∘ eN) r R hR) hz

theorem nonempty_tiledProbeBoxData
    (eN : cartanRootIdeal H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, EN)) N)
    (ExpN : GroupLieAlgebra (𝓘(ℝ, EN)) N → N) (hExpN : IsGroupExponential ExpN)
    (chartN : GroupLieAlgebra (𝓘(ℝ, EN)) N ≃ₜ N) (hchartN : ∀ v, chartN v = ExpN v)
    (dynkinN : NilpotentDynkinExpansionInput EN N)
    (ExpI : M.coneWordIdeal C → I) (ι : I →* N) (hι : Measurable ι)
    (hcompat : ∀ v, ι (ExpI v) = ExpN (eN (v : cartanRootIdeal H)))
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (E : Fin 3 → Set W)
    (hs : ∀ j i, 0 ≤ (M.supportIn T hunimod eW).weightSupport (E j) i)
    (hzero : ∀ j i, (M.weight i : H →ₗ[ℝ] ℝ) ∈ C →
      (M.supportIn T hunimod eW).weightSupport (E j) i = 0)
    (β : Fin 3 → M.ConeIdealBases C)
    (hβ : ∀ j, M.IsMaximizingConeIdealBasis C bI
      ((M.supportIn T hunimod eW).weightSupport (E j)) (β j)) :
    Nonempty (M.TiledProbeBoxData C T hunimod eW eN ExpN ExpI ι bN E β) := by
  obtain ⟨bQ, lift, γ, R₀, hlift, hR₀, hγ, hselect⟩ :=
    M.exists_tiled_probe_boxes C T hunimod eW eN ExpN hExpN chartN hchartN dynkinN
      ExpI ι hι hcompat bN bI E hs hzero β hβ
  exact ⟨⟨bQ, lift, γ, R₀, hlift, hR₀, hγ, hselect⟩⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
