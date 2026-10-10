import OAI.Geometry.SurfaceImmersion.Geometry.ReferenceMetricStability
import OAI.Geometry.SurfaceImmersion.Geometry.SupportJetEquality

namespace OAI

/-! Ordinary first-jet bounds for symmetric tensor components on the fixed
primitive chart supports, including their boundaries. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance tensorReadBoundsFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance tensorReadBoundsFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance tensorReadBoundsDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance tensorReadBoundsDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance tensorReadBoundsSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance tensorReadBoundsSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

def tensorFrameRead (i : B.centers) (u : ∀ p : M, CovariantTwoTensor p)
    (y : JetPolynomial.Base) : TensorFiber :=
  (B.tensorTriv i).continuousLinearMapAt ℝ ((chart (i : M)).symm y)
    (u ((chart (i : M)).symm y))

omit [CompactSpace M] in
lemma tensorFrameRead_smoothOn (i : B.centers) (u : ∀ p : M, CovariantTwoTensor p)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p))) :
    ContDiffOn ℝ ∞ (B.tensorFrameRead i u) (chart (i : M)).target := by
  have h := (B.bundleComponent_smooth_on B.tensorTriv B.tensorTriv_domain i hu).comp
    (chart_symm_smooth (i : M)) (fun _ hx => (chart (i : M)).map_target hx)
  exact h.contDiffOn

lemma tensorFrameRead_jets (i : B.centers) (u : ∀ p : M, CovariantTwoTensor p)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p)))
    (hsym : ∀ p v w, u p v w = u p w v) (m : ℕ)
    {y : JetPolynomial.Base} (hy : y ∈ (B.chartWeightCompact i : Set JetPolynomial.Base)) :
    iteratedFDeriv ℝ m (fiberFromThree ∘ B.tensorChartRead i u) y =
      iteratedFDeriv ℝ m (B.tensorFrameRead i u) y := by
  have hK : tsupport (B.chartWeight i) ⊆ (chart (i : M)).target := by
    rw [B.chartWeight_tsupport]
    rintro _ ⟨p,hp,rfl⟩
    exact (chart (i : M)).map_source (B.weight_support i hp)
  apply iteratedFDeriv_eq_on_tsupport (B.chartWeight_smooth i).continuous
    (chart (i : M)).open_target hK
    (fiberFromThree.contDiff.comp (B.tensorChartRead_smooth i hu)).contDiffOn
    (B.tensorFrameRead_smoothOn i u hu) ?_ m
  · rwa [B.chartWeight_tsupport]
  · intro y hy
    rw [B.chartWeight_tsupport] at hy
    obtain ⟨p,hp,rfl⟩ := hy
    change fiberFromThree (B.tensorChartRead i u (chart (i : M) p)) =
      (B.tensorTriv i).continuousLinearMapAt ℝ ((chart (i : M)).symm (chart (i : M) p))
        (u ((chart (i : M)).symm (chart (i : M) p)))
    rw [(chart (i : M)).left_inv (B.weight_support i hp)]
    exact (B.tensor_frame_read i u hsym hp).symm

theorem tensorFrameRead_C1_bound {D : ℝ} (hD : 0 ≤ D) :
    ∃ E : ℝ, 1 ≤ E ∧ ∀ u : ∀ p : M, CovariantTwoTensor p,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun p => TotalSpace.mk' TensorFiber p (u p)) →
      (∀ p v w, u p v w = u p w v) → B.TensorWeightedBound 1 1 D u →
      ∀ i p, p ∈ tsupport (B.weight i) →
        ‖B.tensorFrameRead i u (chart (i : M) p)‖ ≤ E ∧
        ‖fderiv ℝ (B.tensorFrameRead i u) (chart (i : M) p)‖ ≤ E := by
  classical
  choose R hR hread using fun i : B.centers => B.tensorChartRead_bound i 1
  let E := 1+‖fiberFromThree‖*(∑ i, R i)*D
  have hsum := Finset.sum_nonneg (s := Finset.univ) (fun i _ => hR i)
  have hE : 1 ≤ E := by
    dsimp only [E]
    linarith [mul_nonneg (mul_nonneg (norm_nonneg fiberFromThree) hsum) hD]
  refine ⟨E,hE,?_⟩
  intro u hu hsym hb i p hp
  have h := hread i u 1 D zero_lt_one le_rfl hD hu hb
  have hh := h.linear uniqueDiffOn_univ (by norm_num : (0 : ℝ) ≤ 1)
    (B.tensorChartRead_smooth i hu).contDiffOn fiberFromThree
  have hi : ‖fiberFromThree‖*(R i*D) ≤ E := by
    have hx := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun j _ => hR j) (Finset.mem_univ i)) hD) (norm_nonneg fiberFromThree)
    dsimp only [E]
    nlinarith
  have hj := congrArg norm (B.tensorFrameRead_jets i u hu hsym 0 ⟨p,hp,rfl⟩)
  simp only [norm_iteratedFDeriv_zero] at hj
  have hv := (hh.norm_le (mem_univ (chart (i : M) p))).trans hi
  refine ⟨hj ▸ hv,?_⟩
  have hd := hh.deriv_le zero_lt_one le_rfl (mem_univ (chart (i : M) p))
  simp only [iteratedFDerivWithin_univ,one_pow,div_one] at hd
  rw [B.tensorFrameRead_jets i u hu hsym 1 ⟨p,hp,rfl⟩,
    norm_iteratedFDeriv_one] at hd
  exact hd.trans hi

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
