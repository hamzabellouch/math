import OAI.Geometry.SurfaceImmersion.Atlas.UniformRadiusAtlasIncrement
import OAI.Geometry.SurfaceImmersion.Correction.AtlasPhaseMeanDomains

namespace OAI

/-! Finite mean adjustment gives a small increment uniformly over nearby input maps. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGeometry WeightedEstimates FiniteMean
local instance compactRadiusSmallFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance compactRadiusSmallFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance compactRadiusSmallDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance compactRadiusSmallDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance compactRadiusSmallSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance compactRadiusSmallSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

/-- Compact good phase geometry yields the actual small increment; no
mean data or linear solver is an input. -/
theorem compact_radius_small_increment
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    (Q : A.centers → PhaseBasis) (w : A.centers → Fin 3 → ℝ)
    (hw : ∀ i j, w i j ≠ 0)
    (hImm : ∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
      Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) x))
    (hgood : ∀ i j x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
      Good (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ((Q i).ξ j))
    (reference : ∀ x : M, CovariantTwoTensor x)
    (href : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (reference x)))
    (hpos : ∀ i j x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
      0 < (Q i).Q j (A.tensorPlaneRead i reference x))
    (hgoodQ : ∀ k l x, x ∈ (modeSupport
      (A.quadraticOverlapCompact (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
        (fun a => isClosed_tsupport (A.weight a.1)) k l) : Set SmallModes.Base) →
      Good (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) x)
        (phaseDerivative (coordinatePhase (A.globalQuadraticPhase (A.linearAtlasPhase Q w) k l)) x))
    : ∃ r ρ₀ : ℝ, 0 < r ∧ 0 < ρ₀ ∧
      ∀ (P : ℕ → ℝ), (∀ m, 0 ≤ P m) → ∀ q : ℕ,
      ∀ C : ℕ → ℝ, (∀ m, 1 ≤ C m) →
      ∃ (η₀ : ℝ) (B T : ℕ → ℝ), 0 < η₀ ∧ η₀ ≤ 1 ∧
        (∀ m, 0 ≤ B m) ∧ (∀ m, 0 ≤ T m) ∧
      ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G → ∀ b : ℝ,
        0 ≤ b → b < ρ₀ → A.WeightedBound 1 2 b (G-F) →
      ∀ (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
        (∀ m, A.ShiftedBound 2 m s (P m) G) →
      ∀ (H : ∀ x : M, CovariantTwoTensor x),
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (H x)) →
      (∀ x v v', H x v v' = H x v' v) →
      (∀ x, ‖A.tensorEncode H x - A.tensorEncode reference x‖ ≤ r/2) →
      (∀ m, A.TensorWeightedBound s m (C m) H) →
      ∀ τ δ : ℝ, 0 < τ → τ ≤ s → τ/s ≤ η₀ → 0 < δ → δ ≤ τ →
      ∃ X : M → Space, ContMDiff planeModel spaceModel ∞ X ∧
        (∀ m, A.WeightedBound τ m (B m*(δ*τ)) X) ∧
        (∀ m, A.TensorWeightedBound τ m (T m*(δ*(τ/s)^(q+1)+δ^3/τ))
          (inducedTensor (G+X) - inducedTensor G - δ^2 • H)) := by
  obtain ⟨d⟩ := A.exists_phaseMeanDomains F hF Q hImm hgood
    (fun i => A.tensorPlaneRead i reference)
    (fun i => (A.tensorPlaneRead_smooth i href).continuous) hpos
  apply A.uniform_radius_atlas_increment F hF Q w hw d.Ω d.U d.K
    d.openΩ d.openU d.compactK d.UK d.KΩ d.immersion d.good d.support
    d.U₀ d.openU₀ d.K₀ d.U₀K₀ d.supportU₀ d.r_pos d.ρ_pos reference href d.margin
    ?_ hgoodQ
  intro k l x hx
  apply hImm k x
  exact Set.image_mono (A.quadraticOverlapCompact_subset
    (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
    (fun a => isClosed_tsupport (A.weight a.1)) k l) hx

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
