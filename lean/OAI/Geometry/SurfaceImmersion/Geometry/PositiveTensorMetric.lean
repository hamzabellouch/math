import OAI.Geometry.SurfaceImmersion.Atlas.AtlasMetricBounds

namespace OAI

/-! On the two-dimensional tangent model, a smooth positive symmetric
bilinear tensor is an actual smooth Riemannian metric. -/
noncomputable section
open Set Metric Manifold Bundle Bornology
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing

lemma positive_bilinear_unitBall_bounded (B : Plane →L[ℝ] Plane →L[ℝ] ℝ)
    (hB : ∀ v : Plane, v ≠ 0 → 0 < B v v) :
    IsVonNBounded ℝ {v : Plane | B v v < 1} := by
  have hcpt : IsCompact (sphere (0 : Plane) 1) := isCompact_sphere _ _
  have hf : Continuous (fun v : Plane => B v v) := by fun_prop
  have hp : ∀ v ∈ sphere (0 : Plane) 1, 0 < B v v := by
    intro v hv
    apply hB
    intro hz
    rw [hz] at hv
    norm_num [mem_sphere] at hv
  obtain ⟨c,hc,hbound⟩ := hcpt.exists_forall_le' hf.continuousOn hp
  have hlower (v : Plane) : c*‖v‖^2 ≤ B v v := by
    by_cases hv : v = 0
    · simp [hv]
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hu : ‖‖v‖⁻¹ • v‖ = 1 := by
      simp only [norm_smul,Real.norm_eq_abs,abs_inv,abs_norm]
      exact inv_mul_cancel₀ hn.ne'
    have hh := hbound (‖v‖⁻¹ • v) (by simpa only [mem_sphere,dist_zero_right] using hu)
    have he : B (‖v‖⁻¹ • v) (‖v‖⁻¹ • v)*‖v‖^2 = B v v := by
      simp only [map_smul,smul_apply,smul_eq_mul]
      field_simp
    exact (mul_le_mul_of_nonneg_right hh (sq_nonneg _)).trans_eq he
  apply (NormedSpace.isVonNBounded_ball ℝ Plane (2+c⁻¹)).subset
  intro v hv
  rw [mem_ball,dist_zero_right]
  have hcv : c*‖v‖^2 < 1 := (hlower v).trans_lt hv
  have hinv : 0 < c⁻¹ := inv_pos.mpr hc
  by_cases hn : ‖v‖ ≤ 1
  · linarith
  · have hn1 : 1 < ‖v‖ := lt_of_not_ge hn
    have hsq : ‖v‖ ≤ ‖v‖^2 := by nlinarith
    have hcn : c*‖v‖ < 1 := (mul_le_mul_of_nonneg_left hsq hc.le).trans_lt hcv
    have hnorm : ‖v‖ < c⁻¹ := by
      rw [← one_div]
      exact (lt_div_iff₀ hc).mpr (by simpa [mul_comm] using hcn)
    linarith

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance ptFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance ptFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance ptDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance ptDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance ptSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance ptSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

def positiveTensorMetric (T : ∀ p : M, CovariantTwoTensor p)
    (hT : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (T p)))
    (hsymm : ∀ p v w, T p v w = T p w v)
    (hpos : ∀ p v, v ≠ 0 → 0 < T p v v) : SmoothMetric M where
  inner := T
  symm := hsymm
  pos := hpos
  isVonNBounded p := positive_bilinear_unitBall_bounded (T p) (hpos p)
  contMDiff := hT

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def immersionMetric {F : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F)
    (hI : ∀ p, Function.Injective (mfderiv planeModel spaceModel F p)) : SmoothMetric M :=
  positiveTensorMetric (inducedTensor F) (A.inducedTensor_smooth hF)
    (by
      intro p v w
      change inner ℝ (show Space from mfderiv planeModel spaceModel F p v)
        (show Space from mfderiv planeModel spaceModel F p w) = _
      exact real_inner_comm _ _)
    (by
      intro p v hv
      change 0 < inner ℝ (show Space from mfderiv planeModel spaceModel F p v)
        (show Space from mfderiv planeModel spaceModel F p v)
      apply real_inner_self_pos.mpr
      intro hz
      apply hv
      apply hI p
      rw [map_zero]
      exact hz)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
