import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPolarTiledSamplers
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanDilatedProbeChains
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanAllowedProbeChains
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanLinkedNeighborBoxes
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponentialOperations

namespace OAI

/-! # Linking the actual polar samplers at the original neighboring cells -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric Filter
open scoped Manifold Pointwise Topology

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
  (K : ProperCone ℝ (StrongDual ℝ W))
  [Group I] [TopologicalSpace I] [IsTopologicalGroup I]
  [MeasurableSpace I] [BorelSpace I] [SecondCountableTopology I]


local notation "C" => heightConePreimage T eW K

omit [SimplyConnectedSpace G] [Nonempty (Fin M.letterCount)]
    [IsTopologicalGroup I] [BorelSpace I] [SecondCountableTopology I] in
/-- Dilation and enlarged-box containment turn the stored polar samplers
into the linked chains used by concentration. The logarithmic base points
and their common vanishing error are constructed from the original boxes. -/
theorem PolarTiledSamplerData.linked_chains_from_neighbor_boxes
    (ExpI : M.coneWordIdeal C → I) (ι : I →* F.N.carrier)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {ε : ℝ} (hε : 0 ≤ ε) (β : M.ConeIdealBases C)
    (Rbox : ℝ) (scale : ℕ → ℝ) (φ : ℕ → I ≃ₜ* I)
    (D : M.PolarTiledSamplerData T F hunimod eW K ExpI ι bN ε β Rbox scale φ)
    {Y : ℕ → Type*} [∀ n, MeasurableSpace (Y n)]
    (ψ : ∀ n, Y n →
      (closedBall (0 : Fin (finrank ℝ
        (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) → ℝ) 1) ×
      (M.coneIdealBox C ExpI
        ((M.supportIn T hunimod eW).weightSupport (normalizedPolarTemplates K ε 0))
        β (scale n) 1))
    (hψ : ∀ n, Measurable (ψ n))
    (hbij : Function.Bijective F.ExpN)
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    {Eall : Set W} (hEall : IsCompact Eall) (hne : Eall.Nonempty)
    (γ : M.Bases)
    (hγ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN)
      (M.boxCost T hunimod eW Eall) γ.val)
    (w : W) (hBE : (fun x => x + w) '' normalizedPolarTemplates K ε 1 ⊆ Eall)
    (hw : ∀ i, 0 ≤ (M.supportIn T hunimod eW).weightSupport Eall i)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hs : Tendsto scale atTop atTop) (hs1 : ∀ n, 1 ≤ scale n)
    (R : ℕ → ℝ) (hR0 : ∀ n, 0 ≤ R n)
    (hR : HasSubexponentialUpperBoundSeq scale R)
    (base step : ℕ → F.N.carrier)
    (hbase : ∀ n, base n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun v => (1 + δ) • v) '' Eall) γ (scale n) (R n))
    (hstep : ∀ n, step n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun v => (1 + δ) • v) '' Eall) γ (scale n) (R n)) :
    let S := fun n => integrateNilpotentLieEquiv F.N.equiv F.ExpN hbij dynkinN F.isExpN
      M.bound_zero (cartanIdealWeightDilation T H
        (scale n • cartanHeightSection T H (eW.symm w)))
    let Ep := fun k => (fun x => x + w) '' normalizedPolarTemplates K ε k
    let probe := fun k n y => S n (D.chain.probe n k (ψ n y))
    ∃ (P : ∀ k, M.BoxProbeChains T F hunimod eW bN (Ep k) γ
        (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport Eall i) scale (probe k))
      (origin finish : ℕ → cartanRootIdeal H) (η : ℕ → ℝ),
      (∀ n, F.ExpN (F.N.equiv (origin n)) = base n) ∧
      (∀ n, F.ExpN (F.N.equiv (finish n)) = base n * step n) ∧
      (∀ n, 0 ≤ η n) ∧ Tendsto η atTop (𝓝 0) ∧
      Nonempty (M.LinkedProbeChains T F hunimod eW bN Ep γ
        (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport Eall i)
        scale probe P (fun n _ => origin n) (fun n _ => finish n) η) := by
  classical
  dsimp only
  let E := normalizedPolarTemplates K ε
  have hr (k : Fin 3) : 0 ≤ threePolarRadii ε k := by
    fin_cases k <;> dsimp [threePolarRadii] <;> linarith
  have hEc (k : Fin 3) : IsCompact (E k) :=
    (M.polar_probe_template_properties T hunimod eW K (hr k)).1
  have hEn (k : Fin 3) : (E k).Nonempty :=
    ⟨0, (M.polar_probe_template_properties T hunimod eW K (hr k)).2.2.1⟩
  let raw := Classical.choice (D.largest_width_chains T M F hunimod eW K
    ExpI ι bN hε β Rbox scale φ)
  let P₀ k := BoxProbeChains.reparametrize T M F hunimod eW bN (E k) D.ambient
    ((M.supportIn T hunimod eW).weightSupport (E 1)) scale
    (fun n => D.chain.probe n k) (raw k) ψ hψ
  have hdom (i) : (M.supportIn T hunimod eW).weightSupport ((fun x => x + w) '' E 1) i ≤
      (M.supportIn T hunimod eW).weightSupport Eall i :=
    (M.supportIn T hunimod eW).weightSupport_mono
      ((hEc 1).image (continuous_id.add_const w)) ((hEn 1).image _) hEall hBE i
  let S := fun n => integrateNilpotentLieEquiv F.N.equiv F.ExpN hbij dynkinN F.isExpN
    M.bound_zero (cartanIdealWeightDilation T H
      (scale n • cartanHeightSection T H (eW.symm w)))
  let Ep := fun k => (fun x => x + w) '' E k
  let probe := fun k n y => S n (D.chain.probe n k (ψ n y))
  let P k : M.BoxProbeChains T F hunimod eW bN (Ep k) γ
      (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport Eall i) scale (probe k) :=
    BoxProbeChains.inSamplingBox T M F hunimod eW bN (Ep k) Eall D.ambient γ
      ((M.supportIn T hunimod eW).weightSupport ((fun x => x + w) '' E 1))
      hγ hdom hw hδ scale (fun n => le_trans zero_le_one (hs1 n)) (probe k)
      (BoxProbeChains.dilate T M F hunimod eW hbij dynkinN bN (E k) (E 1)
        (hEc k) (hEn k) (hEc 1) (hEn 1) w D.ambient scale _ (P₀ k))
  obtain ⟨origin, finish, η, ho, hf, hη0, hη, hL⟩ :=
    M.exists_linked_probe_chains_of_neighbor_boxes T F hunimod eW haarN dynkinN bN
      hEall hne γ hγ hδ scale R hs hs1 hR0 hR base step hbase hstep Ep probe P
  exact ⟨P, origin, finish, η, ho, hf, hη0, hη, hL⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
