import OAI.Geometry.SurfaceImmersion.Correction.SmoothedInputCloseness
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasLinearMapBounds
import OAI.Geometry.SurfaceImmersion.Correction.ManifoldSmoothingLinearity

namespace OAI

/-! Low-norm bootstrap assumptions imply the actual smoothed inputs
remain inside the fixed map and tensor neighborhoods. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates

local instance admissibilityFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance admissibilityFiberSpace : NormedSpace ℝ TensorFiber := inferInstance

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

local instance admissibilityDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance admissibilityDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance admissibilitySectionNormed (p : M) :
    NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance admissibilitySectionSpace (p : M) :
    NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem smoothed_input_admissibility (r : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (g : SmoothMetric M) (F G : M → Space) (H : ∀ x : M, CovariantTwoTensor x)
        (ρ a b B t s α K : ℝ),
        0 < ρ → 0 < a → 0 ≤ B → 0 < s → s ≤ t → t ≤ 1 →
        ContMDiff planeModel spaceModel ∞ F → ContMDiff planeModel spaceModel ∞ G →
        ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
          (fun x => TotalSpace.mk' TensorFiber x (H x)) →
        A.InputBound t r B G H → A.WeightedBound 1 2 b (G-F) → b ≤ ρ/4 →
        (∀ x, ‖A.tensorEncode H x - A.tensorEncode g.inner x‖ ≤ a/8) →
        D*B*(s/t)^r ≤ min (ρ/4) (a/8) →
        0 ≤ α → (∀ x, ‖A.tensorEncode g.inner x‖ ≤ K) → α*K ≤ a/8 →
        A.WeightedBound 1 2 (ρ/2) (A.smooth r s G-F) ∧
        ∀ x, ‖A.tensorEncode (A.tensorSmooth r s H - α • g.inner) x -
          A.tensorEncode g.inner x‖ ≤ a/2 := by
  obtain ⟨D,hD,htail⟩ := A.smoothed_input_closeness r
  refine ⟨D,hD,?_⟩
  intro g F G H ρ a b B t s α K _hρ ha hB hs hst ht1 hF hG hH hinput
    hnear hb hHnear hsmall hα hK hαK
  obtain ⟨hmap,htensor⟩ := htail G H B t s hB hs hst ht1 hG hH hinput
  have hsmooth := A.smooth_smooth r hs hG
  have hmapneg : A.WeightedBound 1 2 (D*B*(s/t)^r) (A.smooth r s G-G) := by
    have he : A.smooth r s G-G = (-1 : ℝ) • (G-A.smooth r s G) := by
      funext p
      simp only [Pi.sub_apply,Pi.smul_apply,neg_one_smul]
      abel
    rw [he]
    intro i
    rw [localize_smul]
    rw [neg_one_smul]
    have hnegative := (hmap i).neg uniqueDiffOn_univ
      (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i)
        (hG.sub hsmooth)).contDiffOn
    convert hnegative using 1
  have hsum := A.weightedBound_add (hsmooth.sub hG) (hG.sub hF)
    (show (0 : ℝ) ≤ 1 by norm_num) hmapneg hnear
  change A.WeightedBound 1 2 (D*B*(s/t)^r+b)
    ((A.smooth r s G-G)+(G-F)) at hsum
  have he : (A.smooth r s G-G) + (G-F) = A.smooth r s G-F := by abel
  rw [he] at hsum
  refine ⟨fun i => (hsum i).mono_const (by
    have hsmall' := hsmall.trans (min_le_left _ _)
    linarith),?_⟩
  intro x
  have htail' : ‖A.tensorEncode (A.tensorSmooth r s H) x - A.tensorEncode H x‖ ≤ a/8 := by
    rw [norm_sub_rev]
    exact (htensor x).trans (hsmall.trans (min_le_right _ _))
  have hscalar : ‖α • A.tensorEncode g.inner x‖ ≤ a/8 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hα]
    exact (mul_le_mul_of_nonneg_left (hK x) hα).trans hαK
  rw [A.tensorEncode_sub,A.tensorEncode_smul]
  change ‖(A.tensorEncode (A.tensorSmooth r s H) x - α • A.tensorEncode g.inner x) -
    A.tensorEncode g.inner x‖ ≤ _
  calc
    _ = ‖(A.tensorEncode (A.tensorSmooth r s H) x - A.tensorEncode H x) +
        (A.tensorEncode H x - A.tensorEncode g.inner x) - α • A.tensorEncode g.inner x‖ := by
      congr 1
      abel
    _ ≤ (‖A.tensorEncode (A.tensorSmooth r s H) x - A.tensorEncode H x‖ +
        ‖A.tensorEncode H x - A.tensorEncode g.inner x‖) + ‖α • A.tensorEncode g.inner x‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (a/8+a/8)+a/8 := add_le_add (add_le_add htail' (hHnear x)) hscalar
    _ ≤ a/2 := by linarith

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
