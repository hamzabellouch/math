import OAI.Geometry.SurfaceImmersion.Geometry.GlobalLinearMetricBound
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasMetricBounds
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasLinearMapBounds
import OAI.Geometry.SurfaceImmersion.Correction.ChartedAtlasQuadraticResidual

namespace OAI

/-! Quantitative continuity of the induced metric in a fixed atlas norm. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma inducedTensor_sub_eq_half_linear {F G : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hG : ContMDiff planeModel spaceModel ∞ G) :
    inducedTensor G-inducedTensor F = (1/2 : ℝ) • linearMetricTensor (G+F) (G-F) := by
  funext p
  ext v w
  have ha := mfderiv_add ((hG p).mdifferentiableAt (by simp)) ((hF p).mdifferentiableAt (by simp))
  have hs := mfderiv_sub ((hG p).mdifferentiableAt (by simp)) ((hF p).mdifferentiableAt (by simp))
  change inducedForm G p v w-inducedForm F p v w = (1/2 : ℝ)*linearMetricForm (G+F) (G-F) p v w
  simp only [inducedForm,linearMetricForm,surfaceDifferential,ha,hs]
  let DG : TangentSpace planeModel p →L[ℝ] Space := mfderiv planeModel spaceModel G p
  let DF : TangentSpace planeModel p →L[ℝ] Space := mfderiv planeModel spaceModel F p
  change inner ℝ (DG v) (DG w) -
      inner ℝ (DF v) (DF w) =
    (1/2 : ℝ)*(inner ℝ
      (DG v+DF v)
      (DG w-DF w) +
      inner ℝ (DG v-DF v)
      (DG w+DF w))
  rw [inner_add_left,inner_sub_right,inner_sub_right,inner_sub_left,inner_add_right,inner_add_right]
  ring

variable [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem induced_metric_difference_bound (m : ℕ) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (D eps : ℝ), 0 ≤ D → 0 ≤ eps →
      ∀ F G : M → Space, ContMDiff planeModel spaceModel ∞ F →
        ContMDiff planeModel spaceModel ∞ G →
        A.WeightedBound 1 (m+1) D F → A.WeightedBound 1 (m+1) D G →
        A.WeightedBound 1 (m+1) eps (G-F) →
        A.TensorWeightedBound 1 m (E*D*eps) (inducedTensor G-inducedTensor F) := by
  obtain ⟨E,hE,hbound⟩ := A.global_linear_metric_bound m
  refine ⟨E,hE,?_⟩
  intro D eps hD heps F G hF hG hbF hbG hbDiff
  have hbSum := A.weightedBound_add hG hF zero_le_one hbG hbF
  have hb := hbound 1 (D+D) eps zero_lt_one le_rfl (add_nonneg hD hD) heps
    (G+F) (G-F) (hG.add hF) (hG.sub hF) hbSum hbDiff
  rw [inducedTensor_sub_eq_half_linear hF hG]
  have hs := A.tensorWeightedBound_const_smul (A.linearMetricTensor_smooth (hG.add hF) (hG.sub hF))
    hb (1/2 : ℝ)
  convert hs using 1
  norm_num
  ring

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
