import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNormalizedPolarSamplers
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSourceDilation

namespace OAI

/-! # Counted source samplers using the canonical continuous Cartan dilation -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Filter MeasureTheory
open scoped Manifold Topology

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
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

local notation "C" => heightConePreimage T eW K

/-- The measured source cone determines all group maps and the continuous
dilation. Only the original amplitude bound and the published exponential
inputs are needed to obtain the counted sampler and its exact conjugation
law. Its section is chosen before the scale and neighboring sequence. -/
theorem MeasuredCone.exists_canonical_polar_samplers
    (D : M.MeasuredCone F C)
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (hbijN : Function.Bijective F.ExpN)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (dynkinI : NilpotentDynkinExpansionInput D.I.modelSpace D.I.carrier)
    (haarI : NilpotentExponentialHaarInput D.I.modelSpace D.I.carrier)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (bI : Basis (Fin (finrank ℝ (M.coneWordIdeal C))) ℝ (M.coneWordIdeal C))
    (i : Fin M.letterCount) (hi : (M.weight i : H →ₗ[ℝ] ℝ) ∈ C)
    (pivot : H) (hpivot : 0 < M.weight i pivot)
    (c B ε : ℝ) (hc : 0 ≤ c) (hB : 0 ≤ B) (hε : 0 < ε) :
    let hbijI : Function.Bijective D.maps.expI :=
      funext D.maps.chartI_eq ▸ D.maps.chartI.bijective
    ∃ (β : M.ConeIdealBases C)
      (bQ : Basis (Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)))
        ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule))
      (lift : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) →
        cartanRootIdeal H) (Rbox δ₀ : ℝ),
      (∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (lift j) = bQ j) ∧
      M.IsMaximizingConeIdealBasis C bI (M.polarProbeWidths T hunimod eW K) β ∧
      0 < Rbox ∧ 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (scale : ℕ → ℝ), StrictMono scale → Tendsto scale atTop atTop →
      (∀ n, 0 < scale n) →
      ∀ (radius time : ℕ → ℝ), HasSubexponentialUpperBoundSeq scale radius →
      (∀ n, |time n| ≤ radius n * Real.exp
        ((M.weight i pivot + δ * B) * scale n)) →
      ∀ (step : ℕ → F.N.carrier),
      (∀ n, F.inclusionN (step n) = Exp (time n •
        (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))) →
      ∃ n₀ : ℕ,
        let r := fun n => scale (n + n₀)
        let h := fun n => (r n * (1 - c * δ)) • pivot
        let tn := fun n => Real.exp (-M.weight i (h n)) * time (n + n₀)
        let φ := fun n => M.coneIdealLetterAutomorphism C D.I.equiv D.maps.expI
          D.maps.isExpI hbijI D.maps.chartI D.maps.chartI_eq dynkinI i (tn n)
        ∃ P : M.PolarTiledSamplerData T F hunimod eW K
            (D.maps.expI ∘ D.I.equiv) D.maps.inclusion bN ε β Rbox r φ,
          P.chain.bQ = bQ ∧ P.chain.lift = lift ∧
          ∀ n z, D.maps.inclusion (φ n z) =
            (M.sourceDilation T F hbijN chartN hchartN dynkinN (h n)).symm
                (step (n + n₀)) * D.maps.inclusion z *
              ((M.sourceDilation T F hbijN chartN hchartN dynkinN (h n)).symm
                (step (n + n₀)))⁻¹ := by
  dsimp only
  let b := (finBasis ℝ (M.coneWordIdeal C)).map D.I.equiv.toLinearEquiv
  let coordinates := b.equivFun.symm.toContinuousLinearEquiv.toHomeomorph.trans D.maps.chartI
  let : SecondCountableTopology D.I.carrier := coordinates.symm.secondCountableTopology
  let : IsTopologicalGroup D.I.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, D.I.modelSpace)) ⊤
  have factory : ∃ (β : M.ConeIdealBases C) (μI : MeasureTheory.Measure D.I.carrier)
      (hbij : Function.Bijective D.maps.expI)
      (bQ : Basis (Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)))
        ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule))
      (lift : Fin (finrank ℝ (cartanRootIdeal H ⧸ (M.coneWordIdeal C).toSubmodule)) →
        cartanRootIdeal H) (Rbox δ₀ : ℝ),
      (∀ j, (M.coneWordIdeal C).toSubmodule.mkQ (lift j) = bQ j) ∧
      M.IsMaximizingConeIdealBasis C bI (M.polarProbeWidths T hunimod eW K) β ∧
      μI.IsHaarMeasure ∧ 0 < Rbox ∧ 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (scale : ℕ → ℝ), StrictMono scale → Tendsto scale atTop atTop →
      (∀ n, 0 < scale n) →
      ∀ (radius time : ℕ → ℝ), HasSubexponentialUpperBoundSeq scale radius →
      (∀ n, |time n| ≤ radius n * Real.exp
        ((M.weight i pivot + δ * B) * scale n)) →
      ∀ (S : H → MulAut F.N.carrier),
      (∀ h v, S h (F.ExpN (F.N.equiv v)) =
        F.ExpN (F.N.equiv (cartanIdealWeightDilation T H h v))) →
      ∀ (step : ℕ → F.N.carrier),
      (∀ n, F.inclusionN (step n) = Exp (time n •
        (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))) →
      ∃ n₀ : ℕ,
        let r := fun n => scale (n + n₀)
        let h := fun n => (r n * (1 - c * δ)) • pivot
        let tn := fun n => Real.exp (-M.weight i (h n)) * time (n + n₀)
        let φ := fun n => M.coneIdealLetterAutomorphism C D.I.equiv D.maps.expI D.maps.isExpI hbij D.maps.chartI
          D.maps.chartI_eq dynkinI i (tn n)
        ∃ P : M.PolarTiledSamplerData T F hunimod eW K (D.maps.expI ∘ D.I.equiv) D.maps.inclusion bN ε β Rbox r φ,
          P.chain.bQ = bQ ∧ P.chain.lift = lift ∧
          ∀ n z, D.maps.inclusion (φ n z) =
            (S (h n)).symm (step (n + n₀)) * D.maps.inclusion z *
              ((S (h n)).symm (step (n + n₀)))⁻¹ := by
    exact exists_normalized_polar_samplers (EG := EG) (G := G) (W := W)
      (EI := D.I.modelSpace) (I := D.I.carrier)
      T M F hunimod eW K hExp realize haarN dynkinN
      D.I.equiv D.maps.expI D.maps.isExpI D.maps.chartI D.maps.chartI_eq dynkinI haarI
      D.maps.inclusion D.maps.inclusion_closed.injective
      D.maps.inclusion_closed.continuous.measurable D.maps.inclusion_exp
      bN bI i hi pivot hpivot c B ε hc hB hε
  obtain ⟨β, _, _, bQ, lift, Rbox, δ₀, hlift, hβ, _, hRbox, hδ₀, hsamplers⟩ := factory
  refine ⟨β, bQ, lift, Rbox, δ₀, hlift, hβ, hRbox, hδ₀, ?_⟩
  intro δ hδ hd scale hs hscale hs0 radius time hr ht step hstep
  exact hsamplers δ hδ hd scale hs hscale hs0 radius time hr ht
    (fun h => (M.sourceDilation T F hbijN chartN hchartN dynkinN h).toMulEquiv)
    (M.sourceDilation_apply_exp T F hbijN chartN hchartN dynkinN) step hstep

end PolycyclicRecognition.CartanWordModel

end

end OAI
