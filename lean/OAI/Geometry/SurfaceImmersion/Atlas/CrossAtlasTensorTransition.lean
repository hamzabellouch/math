import OAI.Geometry.SurfaceImmersion.Atlas.CrossAtlasJetRelation
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasTensorTransition

namespace OAI

/-! Actual tensor transitions between independent smoothing atlases. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
open PhaseMean

local instance crossTransitionFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance crossTransitionFiberSpace : NormedSpace ℝ TensorFiber := inferInstance

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

local instance crossTransitionDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance crossTransitionDualSmul : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance crossTransitionSectionNormed (p : M) :
    NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance crossTransitionSectionSpace (p : M) :
    NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A B : SmoothingAtlas M)

def cross_tensorRestoreTransition (i : A.centers) (j : B.centers) (x : Base) : Tensor →L[ℝ] Tensor :=
  B.outer j ((chart (i : M)).symm x) •
    fiberToThree.comp ((((B.tensorTriv j).coordChangeL ℝ (A.tensorTriv i)
      ((chart (i : M)).symm x)) : TensorFiber →L[ℝ] TensorFiber).comp fiberFromThree)

lemma cross_tensorRestoreTransition_smoothOn (i : A.centers) (j : B.centers) :
    ContDiffOn ℝ ∞ (A.cross_tensorRestoreTransition B i j)
      (transition (i : M) (j : M)).source := by
  have hB : ContDiffOn ℝ ∞
      (fun x => ((B.tensorTriv j).coordChangeL ℝ (A.tensorTriv i) ((chart (i : M)).symm x) : TensorFiber →L[ℝ] TensorFiber))
      (transition (i : M) (j : M)).source := by
    apply ContMDiffOn.contDiffOn
    apply (contMDiffOn_coordChangeL (B.tensorTriv j) (A.tensorTriv i)).comp
      ((chart_symm_smooth (i : M)).mono (fun _ hx => hx.1))
    intro x hx
    exact ⟨B.tensorTriv_domain j hx.2,A.tensorTriv_domain i ((chart (i : M)).map_target hx.1)⟩
  have ha : ContDiffOn ℝ ∞ (fun x : Base => B.outer j ((chart (i : M)).symm x))
      (chart (i : M)).target :=
    ((B.outer_smooth j).comp_contMDiffOn (chart_symm_smooth (i : M))).contDiffOn
  have hl : ContDiffOn ℝ ∞ (fun _ : Base => fiberToThree)
      (transition (i : M) (j : M)).source := contDiffOn_const
  have hr : ContDiffOn ℝ ∞ (fun _ : Base => fiberFromThree)
      (transition (i : M) (j : M)).source := contDiffOn_const
  exact (ha.mono (fun _ hx => hx.1)).smul (hl.clm_comp (hB.clm_comp hr))

lemma cross_tensorChartRead_restoreThree (i : A.centers) (j : B.centers) (f : Base → Tensor)
    {x : Base} (hx : x ∈ (transition (i : M) (j : M)).source)
    (ho : A.outer i ((chart (i : M)).symm x) = 1) :
    A.tensorChartRead i (B.bundleRestore B.tensorTriv j (fun y => fiberFromThree (f y))) x =
      A.cross_tensorRestoreTransition B i j x (f (transition (i : M) (j : M) x)) := by
  have hxt : x ∈ (chart (i : M)).target := hx.1
  have hbi := A.tensorTriv_domain i ((chart (i : M)).map_target hx.1)
  have hj : (chart (i : M)).symm x ∈ (chart (j : M)).source := hx.2
  have hbj := B.tensorTriv_domain j hj
  simp only [tensorChartRead,Function.comp_apply,bundleCutoff,bundleComponent,localize,
    indicator_of_mem hxt,bundleRestore,map_smul,ho,one_pow,one_smul]
  rw [(A.tensorTriv i).continuousLinearMapAt_apply_of_mem ℝ hbi,
    (B.tensorTriv j).symmL_apply (R := ℝ) hbj,
    ← (B.tensorTriv j).coordChangeL_apply (R := ℝ) (A.tensorTriv i) ⟨hbj,hbi⟩]
  rfl

lemma cross_tensorChartRead_restore_zero (i : A.centers) (j : B.centers) (f : Base → TensorFiber)
    {x : Base} (hx : x ∈ (chart (i : M)).target)
    (hz : B.outer j ((chart (i : M)).symm x) = 0) :
    A.tensorChartRead i (B.bundleRestore B.tensorTriv j f) x = 0 := by
  simp only [tensorChartRead,Function.comp_apply,bundleCutoff,localize,
    indicator_of_mem hx,bundleComponent,bundleRestore,hz,zero_smul,map_zero,smul_zero]

theorem cross_compact_tensorRestoreTransition (i : A.centers) (j : B.centers) {K : Set Base}
    (hK : IsCompact K) (hKe : K ⊆ (transition (i : M) (j : M)).source) :
    ∃ U : Set Base, IsOpen U ∧ K ⊆ U ∧
      U ⊆ (transition (i : M) (j : M)).source ∧
      ∃ L : Base → Tensor →L[ℝ] Tensor, ContDiff ℝ ∞ L ∧
        EqOn L (A.cross_tensorRestoreTransition B i j) U :=
  CollarVelocity.compact_smooth_extension hK (transition (i : M) (j : M)).open_source hKe
    (A.cross_tensorRestoreTransition_smoothOn B i j)

def cross_pairSupport (i : A.centers) (j : B.centers) : Set Base :=
  (chart (i : M)) '' (tsupport (A.weight i) ∩ tsupport (B.outer j))

variable [CompactSpace M]
lemma cross_pairSupport_compact (i : A.centers) (j : B.centers) :
    IsCompact (A.cross_pairSupport B i j) :=
  ((isClosed_tsupport (A.weight i)).inter (isClosed_tsupport (B.outer j))).isCompact.image_of_continuousOn
    ((chart (i : M)).continuousOn.mono (fun _ hx => A.weight_support i hx.1))

omit [CompactSpace M] in
lemma cross_pairSupport_transition (i : A.centers) (j : B.centers) :
    A.cross_pairSupport B i j ⊆ (transition (i : M) (j : M)).source := by
  rintro x ⟨p,⟨hp,hq⟩,rfl⟩
  have hp' := A.weight_support i hp
  refine ⟨(chart (i : M)).map_source hp',?_⟩
  change (chart (i : M)).symm (chart (i : M) p) ∈ (chart (j : M)).source
  rw [(chart (i : M)).left_inv hp']
  exact B.outer_support j hq

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
