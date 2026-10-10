import OAI.Geometry.SurfaceImmersion.Correction.AtlasGlobalFreeModes
import OAI.Geometry.SurfaceImmersion.Atlas.SupportedAtlasDifferential

namespace OAI

/-! Actual global free amplitudes retain the original geometric supports. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma freeGlobalAmplitude_tsupport
    {n : A.centers → ℕ} {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
    {ε τ : ℝ} {s : ℝ≥0} {r : A.centers → ℝ} {ρ R : ℝ}
    {reference : A.centers → SmallModes.Base → Tensor}
    (d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (r i) ρ R (reference i))
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x)
    (hK : ∀ i j, (modeSupport ((d i).support j) : Set SmallModes.Base) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
    (i : A.centers) (j : Fin 3) :
    tsupport (A.freeGlobalAmplitude d hρ δ q u i j) ⊆ tsupport (A.weight i) := by
  have hs := (coordinateAmplitude_support
    ((d i).data j |>.freeAmplitude hρ δ q (A.tensorPlaneRead i u))).trans (hK i j)
  have hh := A.restore_plane_tsupport i
    (coordinateAmplitude ((d i).data j |>.freeAmplitude hρ δ q (A.tensorPlaneRead i u))) hs
  simpa only [freeGlobalAmplitude,coordinateAmplitude,Function.comp_def,
    LinearIsometryEquiv.symm_apply_apply] using hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
