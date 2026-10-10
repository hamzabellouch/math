import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPolarLinkedSource
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanTiledSourceEndpoints
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSourceDilation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.LinkedRootProbeFrames

namespace OAI

/-! # Actual linked frames on the counted polar source cell -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric Filter
open scoped Manifold Pointwise Topology

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  (K : ProperCone ℝ (StrongDual ℝ W))

local notation "C" => heightConePreimage T eW K

variable (D : M.MeasuredCone F (heightConePreimage T eW K))
  (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
  {ε : ℝ} (β : M.ConeIdealBases (heightConePreimage T eW K)) (Rbox : ℝ) (scale : ℕ → ℝ)
  (φ : ℕ → D.I.carrier ≃ₜ* D.I.carrier)
  (P : M.PolarTiledSamplerData (EG := EG) (G := G) (W := W) (I := D.I.carrier) T F hunimod eW K
    (fun v : M.coneWordIdeal (heightConePreimage T eW K) => D.maps.expI (D.I.equiv v)) D.maps.inclusion bN ε β Rbox scale φ)
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)

local notation "ZQ" => TiledProbeChainData.sourceQuotientCell
  (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) («C» := C)
  (ExpI := D.maps.expI ∘ D.I.equiv) (bN := bN)
  (E := normalizedPolarTemplates K ε) (β := fun _ => β) (ambient := P.ambient)
  (t := fun i => ε * M.polarProbeWidths T hunimod eW K i)
  (scale := scale) (φ := φ) (ι := D.maps.inclusion)
  (tiles := P.tiles) (anchor := P.anchor) (D := P.chain)
  (Q := D.Q) (chartQ := D.maps.chartQ)
local notation "J" => fun n => TiledProbeChainData.sourceKernelCell
  (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) («C» := C)
  (ExpI := D.maps.expI ∘ D.I.equiv) (E := normalizedPolarTemplates K ε)
  (β := fun _ => β) (scale := scale) (ι := D.maps.inclusion)
  (Q := D.Q) (πQ := D.maps.quotient) (hι := D.maps.inclusion_closed)
  (hrange := D.maps.inclusion_range) n
local notation "Y" => fun n : ℕ => {p : D.Q.carrier × D.maps.quotient.ker // p ∈ Set.prod ZQ (J n)}
local notation "ψ" => fun n => TiledProbeChainData.sourceCoordinates
  (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) («C» := C)
  (ExpI := D.maps.expI ∘ D.I.equiv) (bN := bN)
  (E := normalizedPolarTemplates K ε) (β := fun _ => β) (ambient := P.ambient)
  (t := fun i => ε * M.polarProbeWidths T hunimod eW K i)
  (scale := scale) (φ := φ) (ι := D.maps.inclusion)
  (tiles := P.tiles) (anchor := P.anchor) (D := P.chain)
  (Q := D.Q) (chartQ := D.maps.chartQ) (πQ := D.maps.quotient)
  (hι := D.maps.inclusion_closed) (hrange := D.maps.inclusion_range) n
local notation "σ" => TiledProbeChainData.sourceSection
  (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) («C» := C)
  (ExpI := D.maps.expI ∘ D.I.equiv) (bN := bN)
  (E := normalizedPolarTemplates K ε) (β := fun _ => β) (ambient := P.ambient)
  (t := fun i => ε * M.polarProbeWidths T hunimod eW K i)
  (scale := scale) (φ := φ) (ι := D.maps.inclusion)
  (tiles := P.tiles) (anchor := P.anchor) (D := P.chain)
  (Q := D.Q) (chartQ := D.maps.chartQ) (chartN := chartN)

variable (Eall : Set W) (γ : M.Bases) (δ : ℝ) (w : W)
  (S : ℕ → F.N.carrier ≃ₜ* F.N.carrier) (base step : ℕ → F.N.carrier)

local notation "Ep" => fun k => (fun z => z + w) '' normalizedPolarTemplates K ε k
local notation "width" => fun i => (1 + δ) * SupportDatum.weightSupport (M.supportIn T hunimod eW) Eall i
local notation "probe" => fun k n (y : Y n) => S n (P.chain.probe n k (ψ n y))

/-- The linked frames on this exact source cell. -/
abbrev PolarTiledSamplerData.LinkedSource :=
  LinkedRootProbeFrames («Y» := Y) T M F hunimod eW bN Ep γ width scale probe base step
    (fun n (y : Y n) => base n * S n ((y.val.2 : F.N.carrier) * σ y.val.1))
    (fun n (y : Y n) => coneProbeSecond (S n).toMulEquiv (base n)
      (D.maps.inclusion (P.anchor n (P.chain.index n (ψ n y).2))) ((S n).symm (step n)))
    (fun n (y : Y n) => coneProbeSecond (S n).toMulEquiv (base n)
      (y.val.2 : F.N.carrier) ((S n).symm (step n)))

omit Eall γ δ w S base step in
/-- The section kept by the counted source sampler is a right inverse of
its actual quotient homomorphism. -/
theorem PolarTiledSamplerData.source_section_rightInverse
    (hchartN : ∀ v, chartN v = F.ExpN v) :
    ∀ q, D.maps.quotient (σ q) = q := by
  apply TiledProbeChainData.sourceSection_rightInverse
    (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) («C» := C)
    (ExpI := D.maps.expI ∘ D.I.equiv) (bN := bN)
    (E := normalizedPolarTemplates K ε) (β := fun _ => β) (ambient := P.ambient)
    (t := fun i => ε * M.polarProbeWidths T hunimod eW K i)
    (scale := scale) (φ := φ) (ι := D.maps.inclusion)
    (tiles := P.tiles) (anchor := P.anchor) (D := P.chain)
    (Q := D.Q) (chartQ := D.maps.chartQ) (chartN := chartN)
    (πQ := D.maps.quotient)
  intro v
  rw [hchartN, D.maps.quotient_exp, D.maps.chartQ_eq]
  rfl

omit Eall γ δ w S base step in
/-- The prescribed polar sampler and original neighboring boxes construct
all linked source frames, including their exact counted tile endpoints. -/
theorem PolarTiledSamplerData.nonempty_linkedSource
    (hε : 0 ≤ ε)
    (hbijN : Function.Bijective F.ExpN)
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    {Eall : Set W} (hEall : IsCompact Eall) (hne : Eall.Nonempty)
    (γ : M.Bases)
    (hγ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN)
      (M.boxCost T hunimod eW Eall) γ.val)
    (w : W) (hBE : (fun z => z + w) '' normalizedPolarTemplates K ε 1 ⊆ Eall)
    (hw : ∀ i, 0 ≤ (M.supportIn T hunimod eW).weightSupport Eall i)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hs : Tendsto scale atTop atTop) (hs1 : ∀ n, 1 ≤ scale n)
    (R : ℕ → ℝ) (hR0 : ∀ n, 0 ≤ R n) (hR : HasSubexponentialUpperBoundSeq scale R)
    (base step : ℕ → F.N.carrier)
    (hbase : ∀ n, base n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun v => (1 + δ) • v) '' Eall) γ (scale n) (R n))
    (hstep : ∀ n, step n ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun v => (1 + δ) • v) '' Eall) γ (scale n) (R n))
    (hφ : ∀ n z, D.maps.inclusion (φ n z) =
      (M.sourceDilation T F hbijN chartN hchartN dynkinN
        (scale n • cartanHeightSection T H (eW.symm w))).symm (step n) *
      D.maps.inclusion z *
      ((M.sourceDilation T F hbijN chartN hchartN dynkinN
        (scale n • cartanHeightSection T H (eW.symm w))).symm (step n))⁻¹) :
    Nonempty (P.LinkedSource T M F hunimod eW K D bN β Rbox scale φ chartN
      Eall γ δ w
      (fun n => M.sourceDilation T F hbijN chartN hchartN dynkinN
        (scale n • cartanHeightSection T H (eW.symm w))) base step) := by
  let S := fun n => M.sourceDilation T F hbijN chartN hchartN dynkinN
    (scale n • cartanHeightSection T H (eW.symm w))
  let bI := (finBasis ℝ (M.coneWordIdeal C)).map D.I.equiv.toLinearEquiv
  let coordI := bI.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans D.maps.chartI
  let : SecondCountableTopology D.I.carrier := coordI.symm.secondCountableTopology
  let bQ := (finBasis ℝ ((cartanRootIdeal H) ⧸ M.coneWordIdeal C)).map D.Q.equiv.toLinearEquiv
  let coordQ := bQ.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans D.maps.chartQ
  let : SecondCountableTopology D.Q.carrier := coordQ.symm.secondCountableTopology
  let : IsTopologicalGroup D.I.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, D.I.modelSpace)) ⊤
  obtain ⟨chains, origin, finish, error, ho, hf, he0, he, ⟨linked⟩⟩ :=
    PolarTiledSamplerData.linked_chains_from_neighbor_boxes T M F hunimod eW K
      (fun v : M.coneWordIdeal C => D.maps.expI (D.I.equiv v)) D.maps.inclusion bN hε β Rbox scale φ P ψ
      (fun n => (ψ n).continuous.measurable) hbijN haarN dynkinN hEall hne γ hγ
      w hBE hw hδ hs hs1 R hR0 hR base step hbase hstep
  have hend (n) (y : Y n) := TiledProbeChainData.source_linked_endpoints
    (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) («C» := C)
    (ExpI := D.maps.expI ∘ D.I.equiv) (bN := bN)
    (E := normalizedPolarTemplates K ε) (β := fun _ => β) (ambient := P.ambient)
    (t := fun i => ε * M.polarProbeWidths T hunimod eW K i)
    (scale := scale) (φ := φ) (ι := D.maps.inclusion)
    (tiles := P.tiles) (anchor := P.anchor) (D := P.chain)
    (Q := D.Q) (chartQ := D.maps.chartQ) (chartN := chartN)
    (πQ := D.maps.quotient) (hι := D.maps.inclusion_closed)
    (hrange := D.maps.inclusion_range) hchartN (fun n => (S n).symm (step n)) base hφ
    (fun n => (S n).toMulEquiv)
    (fun k => (fun z => z + w) '' normalizedPolarTemplates K ε k) γ
    (fun i => (1 + δ) * (M.supportIn T hunimod eW).weightSupport Eall i)
    chains origin finish error linked ho
    (fun n => (hf n).trans (congrArg (fun z => base n * z)
      ((S n).apply_symm_apply (step n)).symm)) n y
  exact ⟨{
    origin := origin, finish := finish, error := error
    error_nonneg := he0, error_tendsto := he, chains := chains, linked := linked
    origin_eq := ho, finish_eq := hf
    first_endpoint := fun n y => (hend n y).1
    anchor_endpoint := fun n y => (hend n y).2.1
    second_endpoint := fun n y => (hend n y).2.2 }⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI
