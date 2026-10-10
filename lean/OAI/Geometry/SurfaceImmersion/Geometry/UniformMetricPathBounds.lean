import OAI.Geometry.SurfaceImmersion.Geometry.ShortMetricPath
import OAI.Geometry.SurfaceImmersion.Geometry.ScaledInitialMap
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasNormalizationBounds

namespace OAI

/-! First-order metric bounds fixed before finite spherical modifications. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance pathBoundFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance pathBoundFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance pathBoundDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance pathBoundDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance pathBoundSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance pathBoundSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma exists_tensorWeighted_bound (m : ℕ) {T : ∀ p : M, CovariantTwoTensor p}
    (hT : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (T p))) :
    ∃ C : ℝ, 0 ≤ C ∧ A.TensorWeightedBound 1 m C T := by
  classical
  choose C hC hb using fun i : A.centers => compact_smooth_bound
    (A.bundleLocalize_smooth A.tensorTriv A.tensorTriv_domain i hT)
    (localize_compact (i : M) (A.weight_support i) (A.bundleComponent A.tensorTriv i T)) m
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), fun i => ?_⟩
  exact (hb i).mono_const (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i))

lemma uniform_induced_tensor_bound {C : ℝ} (hC : 0 ≤ C) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ F : M → Space, ContMDiff planeModel spaceModel ∞ F →
      A.WeightedBound 1 (m+1) C F → A.TensorWeightedBound 1 m D (inducedTensor F) := by
  obtain ⟨D,hD,hbound⟩ := A.global_cubic_remainder_bound m 0 C le_rfl hC
  refine ⟨D,hD,fun F hF hb => ?_⟩
  have hz : A.WeightedBound 1 (m+1) (0*(1*1)) (0 : M → Space) := by
    intro i
    simp only [zero_mul]
    change WeightedEstimates.WeightedBound univ 1 (m+1) 0 (localize (i : M) (A.weight i) 0)
    have he : localize (i : M) (A.weight i) (0 : M → Space) = 0 := by
      funext x
      by_cases hx : x ∈ (chart (i : M)).target <;> simp [localize,hx]
    rw [he]
    exact weightedBound_zero univ 1 (m+1)
  have ht := hbound 1 1 zero_lt_one le_rfl zero_le_one le_rfl 0 F
    contMDiff_const hF hz (by simpa only [one_pow,mul_one] using hb)
  have he : linearMetricTensor (0 : M → Space) F = 0 := by
    funext p
    ext v w
    change inner ℝ (show Space from mfderiv planeModel spaceModel (0 : M → Space) p v)
        (show Space from mfderiv planeModel spaceModel F p w) +
      inner ℝ (show Space from mfderiv planeModel spaceModel F p v)
        (show Space from mfderiv planeModel spaceModel (0 : M → Space) p w) = 0
    have hd : (mfderiv planeModel spaceModel (fun _ : M => (0 : Space)) p :
        TangentSpace planeModel p →L[ℝ] Space) = 0 := mfderiv_const
    change inner ℝ ((mfderiv planeModel spaceModel (fun _ : M => (0 : Space)) p) v)
        (show Space from mfderiv planeModel spaceModel F p w) +
      inner ℝ (show Space from mfderiv planeModel spaceModel F p v)
        ((mfderiv planeModel spaceModel (fun _ : M => (0 : Space)) p) w) = 0
    rw [hd]
    change inner ℝ (0 : Space) (show Space from mfderiv planeModel spaceModel F p w) +
      inner ℝ (show Space from mfderiv planeModel spaceModel F p v) (0 : Space) = 0
    rw [inner_zero_left,inner_zero_right,add_zero]
  simpa only [he,zero_add,one_pow,div_one,mul_one] using ht

lemma uniform_short_path_tensor_bound (g : SmoothMetric M) {C : ℝ} (hC : 0 ≤ C)
    (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
      (hI : ∀ p, Function.Injective (mfderiv planeModel spaceModel F p))
      (hshort : ∀ p v, inducedForm F p v v ≤ (1/2 : ℝ)*g.inner p v v),
      A.WeightedBound 1 (m+1) C F → ∀ s : ℝ, ∀ hs : 0 ≤ s, s ≤ 1 →
      A.TensorWeightedBound 1 m D (A.shortPathMetric g hF hshort hI s hs).inner := by
  obtain ⟨D,hD,hb⟩ := A.uniform_induced_tensor_bound hC m
  obtain ⟨E,hE,he⟩ := A.exists_tensorWeighted_bound m g.contMDiff
  refine ⟨D+E,add_nonneg hD hE,?_⟩
  intro F hF hI hshort hFC s hs hs1
  have hleft := A.tensorWeightedBound_const_smul (A.inducedTensor_smooth hF) (hb F hF hFC) (1-s)
  have hright := A.tensorWeightedBound_const_smul g.contMDiff he s
  have hsum := A.tensorWeightedBound_add (A.inducedTensor_smooth hF).const_smul_section
    g.contMDiff.const_smul_section zero_le_one hleft hright
  have hid : (A.shortPathMetric g hF hshort hI s hs).inner =
      (1-s) • inducedTensor F+s • g.inner := by
    funext p
    ext v w
    exact A.shortPathMetric_apply g hF hshort hI s hs p v w
  rw [hid]
  intro i
  apply (hsum i).mono_const
  rw [abs_of_nonneg (sub_nonneg.mpr hs1),abs_of_nonneg hs]
  nlinarith

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
