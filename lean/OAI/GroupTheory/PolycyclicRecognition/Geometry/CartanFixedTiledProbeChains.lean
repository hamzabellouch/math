import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTiledProbeChains

namespace OAI

/-! # Tiled chains retain the quotient section chosen before the small parameter -/

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


omit [SimplyConnectedSpace G] [FiniteDimensional ℝ W] [Nonempty (Fin M.letterCount)]
    [IsTopologicalGroup I] [BorelSpace I] [SecondCountableTopology I] in
theorem exists_tiled_samplers_from_box
    (ExpI : M.coneWordIdeal C → I) (ι : I →* F.N.carrier)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Fin 3 → Set W)
    (β : Fin 3 → M.ConeIdealBases C)
    (data : M.TiledProbeBoxData C T hunimod eW F.N.equiv F.ExpN ExpI ι bN E β)
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
    ∃ (index : ∀ n, U n → Fin (tiles n)) (probe : ∀ n, Fin 3 → Z × U n → F.N.carrier),
      (∀ n, Measurable (index n)) ∧ (∀ n j, Measurable (probe n j)) ∧
      (∀ n j y, probe n j y ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
        (E j) (data.γ j) (scale n) (![data.R₀, 1, R] j)) ∧
      (∀ n y, probe n 0 y = ι y.2.val * F.ExpN (F.N.equiv
        (quotientLinearSection (M.coneWordIdeal C) data.bQ data.lift
          (data.bQ.equivFun.symm y.1.val)))) ∧
      (∀ n y, probe n 1 y = ι ((φ n).symm (anchor n (index n y.2)))) ∧
      ∀ n y, probe n 2 y = ι ((φ n).symm ((anchor n (index n y.2))⁻¹ * y.2.val)) := by
  classical
  dsimp only
  have hboxes := data.select
  have hex (n : ℕ) := hboxes (scale n) (hr n) R hR
    (φ n) (k n) (hφ n) (tiles n) (anchor n) (tile n) (hm n) (hd n) (hu n) (ha n) (ht n)
  choose index probe properties using hex
  refine ⟨index, probe, fun n => (properties n).1,
    fun n => (properties n).2.1, fun n => (properties n).2.2.1, fun n => (properties n).2.2.2.1,
    fun n => (properties n).2.2.2.2.1, fun n => (properties n).2.2.2.2.2⟩

omit [IsTopologicalGroup I] [BorelSpace I] [SecondCountableTopology I] in
theorem exists_tiled_probe_values_from_box
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (ExpI : M.coneWordIdeal C → I) (ι : I →* F.N.carrier)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Fin 3 → Set W) (hE : ∀ j, IsCompact (E j)) (hne : ∀ j, (E j).Nonempty)
    (β : Fin 3 → M.ConeIdealBases C)
    (data : M.TiledProbeBoxData C T hunimod eW F.N.equiv F.ExpN ExpI ι bN E β)
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
    ∃ (index : ∀ n, U n → Fin (tiles n)) (probe : ∀ n, Fin 3 → Z × U n → F.N.carrier),
      (∀ n, Measurable (index n)) ∧ (∀ n j, Measurable (probe n j)) ∧
      (∀ j, Nonempty (M.BoxProbeChains T F hunimod eW bN (E j) ambient t scale
        (fun n => probe n j))) ∧
      (∀ n y, probe n 0 y = ι y.2.val * F.ExpN (F.N.equiv
        (quotientLinearSection (M.coneWordIdeal C) data.bQ data.lift
          (data.bQ.equivFun.symm y.1.val)))) ∧
      (∀ n y, probe n 1 y = ι ((φ n).symm (anchor n (index n y.2)))) ∧
      ∀ n y, probe n 2 y = ι ((φ n).symm ((anchor n (index n y.2))⁻¹ * y.2.val)) := by
  classical
  dsimp only
  obtain ⟨index, probe, hi, hp, hb, hf, hs, ht⟩ :=
    M.exists_tiled_samplers_from_box T F hunimod eW C ExpI ι bN E β data
      scale hr R hR φ k hφ tiles anchor tile hm hd hu ha ht
  refine ⟨index, probe, hi, hp, ?_, hf, hs, ht⟩
  intro j
  have hrad : 0 ≤ (![data.R₀, 1, R] j) := by
    fin_cases j
    · exact data.radius_nonneg
    · exact zero_le_one
    · exact hR
  exact M.nonempty_boxProbeChains T F hunimod eW hExp realize haarN dynkinN
    bN (E j) (hE j) (hne j) (![data.R₀, 1, R] j) hrad (data.γ j) ambient
    (data.maximizing j) t (hdom j) hambient scale hr (fun n => probe n j)
    (fun n => hp n j) (fun n q => hb n j q)

omit [IsTopologicalGroup I] [BorelSpace I] [SecondCountableTopology I] in
theorem exists_tiled_probe_chains_from_box
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (ExpI : M.coneWordIdeal C → I) (ι : I →* F.N.carrier)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Fin 3 → Set W) (hE : ∀ j, IsCompact (E j)) (hne : ∀ j, (E j).Nonempty)
    (β : Fin 3 → M.ConeIdealBases C)
    (data : M.TiledProbeBoxData C T hunimod eW F.N.equiv F.ExpN ExpI ι bN E β)
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
    ∃ D : M.TiledProbeChainData T F hunimod eW C ExpI bN E β ambient t
      scale φ ι tiles anchor, D.bQ = data.bQ ∧ D.lift = data.lift := by
  obtain ⟨index, probe, hi, hp, hc, hf, hs, ht⟩ :=
    M.exists_tiled_probe_values_from_box T F hunimod eW C hExp realize haarN dynkinN
      ExpI ι bN E hE hne β data ambient t hdom hambient scale hr R hR φ k hφ
      tiles anchor tile hm hd hu ha ht
  exact ⟨⟨data.bQ, data.lift, index, probe, data.lifts, hi, hp, hc, hf, hs, ht⟩, rfl, rfl⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
