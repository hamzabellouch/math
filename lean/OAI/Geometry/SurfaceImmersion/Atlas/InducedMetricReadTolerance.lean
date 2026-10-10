import OAI.Geometry.SurfaceImmersion.Geometry.InducedMetricDifferenceBound
import OAI.Geometry.SurfaceImmersion.Atlas.IndependentTensorReadTolerance
import OAI.Geometry.SurfaceImmersion.Geometry.ScaledInitialMap
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasNormalizationBounds

namespace OAI

/-! The finite-point C1 accuracy makes the actual scaled metric arbitrarily
close to its fixed reference in every primitive chart. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A B : SmoothingAtlas M)

theorem induced_metric_read_tolerance {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (r : ℝ) {eta : ℝ} (heta : 0 < eta) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ G : M → Space,
      ContMDiff planeModel spaceModel ∞ G → A.WeightedBound 1 1 eps (G-F) →
      ∀ (i : B.centers) (y : JetPolynomial.Base),
        ‖B.tensorChartRead i (inducedTensor (r • G)-inducedTensor (r • F)) y‖ < eta := by
  obtain ⟨C,hC,hFb⟩ := A.exists_weighted_bound 1 hF
  obtain ⟨E,hE,hmetric⟩ := A.induced_metric_difference_bound 0
  obtain ⟨delta,hdelta,hread⟩ := A.tensor_read_tolerance B heta
  let K := r^2*E*(C+1)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let eps := min 1 (delta/(K+1))
  have heps : 0 < eps := lt_min zero_lt_one (div_pos hdelta (by linarith))
  have hKe : K*eps ≤ delta := by
    have hh := (le_div_iff₀ (by linarith : 0 < K+1)).mp (min_le_right 1 (delta/(K+1)))
    nlinarith
  refine ⟨eps,heps,?_⟩
  intro G hG hclose i y
  have hGb : A.WeightedBound 1 1 (C+1) G := by
    have hh := A.weightedBound_add hF (hG.sub hF) zero_le_one hFb hclose
    have heq : F+(G-F) = G := by abel
    change A.WeightedBound 1 1 (C+eps) (F+(G-F)) at hh
    rw [heq] at hh
    exact fun i => (hh i).mono_const (by have hh : eps ≤ 1 := min_le_left _ _; linarith)
  have hFb' : A.WeightedBound 1 1 (C+1) F := fun i => (hFb i).mono_const (by linarith)
  have hb := hmetric (C+1) eps (by linarith) heps.le F G hF hG hFb' hGb hclose
  have hs := A.tensorWeightedBound_const_smul
    ((A.inducedTensor_smooth hG).sub_section (A.inducedTensor_smooth hF)) hb (r^2)
  have heq : inducedTensor (r • G)-inducedTensor (r • F) =
      r^2 • (inducedTensor G-inducedTensor F) := by
    rw [inducedTensor_const_smul hG r,inducedTensor_const_smul hF r]
    funext p
    ext v w
    change r^2*inducedTensor G p v w-r^2*inducedTensor F p v w =
      r^2*(inducedTensor G p v w-inducedTensor F p v w)
    ring
  have hb' : A.TensorWeightedBound 1 0 delta (inducedTensor (r • G)-inducedTensor (r • F)) := by
    rw [heq]
    intro a
    apply (hs a).mono_const
    rw [abs_of_nonneg (sq_nonneg r)]
    calc
      r^2*(E*(C+1)*eps) = K*eps := by dsimp [K]; ring
      _ ≤ delta := hKe
  have hGs : ContMDiff planeModel spaceModel ∞ (r • G) :=
    (show ContMDiff planeModel 𝓘(ℝ) ∞ (fun _ : M => r) from contMDiff_const).smul hG
  have hFs : ContMDiff planeModel spaceModel ∞ (r • F) :=
    (show ContMDiff planeModel 𝓘(ℝ) ∞ (fun _ : M => r) from contMDiff_const).smul hF
  exact hread _ ((A.inducedTensor_smooth hGs).sub_section (A.inducedTensor_smooth hFs)) hb' i y

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
