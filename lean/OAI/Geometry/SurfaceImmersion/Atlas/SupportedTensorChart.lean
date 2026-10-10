import OAI.Geometry.SurfaceImmersion.Atlas.SupportedChartEquiv
import OAI.Geometry.Immersion.ClosedSurface.PullbackBounds

namespace OAI

/-! Coordinate transport of the symmetric complex tensors used as targets
in the perturbed phase equations. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates PhaseMean

variable (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (K : Compacts SmallModes.Base) (hK : (K : Set SmallModes.Base) ⊆ e.source)

lemma tensorChartPush_zero (f : SupportedField (F := ComplexTensor) K) :
    ∀ y ∈ e.target, y ∉ (chartSupport e K hK : Set SmallModes.Base) →
      coordinateTarget e.symm f y = 0 := by
  intro y hy hn
  simp only [coordinateTarget, chartPush_zero e K hK f y hy hn, map_zero]

def tensorChartPush (f : SupportedField (F := ComplexTensor) K) :
    SupportedField (F := ComplexTensor) (chartSupport e K hK) :=
  ContDiffMapSupportedIn.of_support_subset
    (contDiff_indicator_of_support e.open_target (chartSupport e K hK).isCompact.isClosed
      (chartSupport_subset e K hK)
      (contDiffOn_coordinateTarget e.open_target f.contDiff.contDiffOn hi (fun _ _ => Set.mem_univ _))
      (tensorChartPush_zero e K hK f))
    (subset_closure.trans (tsupport_indicator_subset (chartSupport e K hK).isCompact.isClosed
      (tensorChartPush_zero e K hK f)))

@[simp] lemma tensorChartPush_apply (f : SupportedField (F := ComplexTensor) K) (y : SmallModes.Base) :
    tensorChartPush e hi K hK f y = e.target.indicator (coordinateTarget e.symm f) y := rfl

def tensorChartPushLM :
    SupportedField (F := ComplexTensor) K →ₗ[ℝ] SupportedField (F := ComplexTensor) (chartSupport e K hK) where
  toFun := tensorChartPush e hi K hK
  map_add' f g := by
    apply DFunLike.ext
    intro y
    by_cases hy : y ∈ e.target <;>
      simp [tensorChartPush_apply, hy, coordinateTarget, map_add]
  map_smul' c f := by
    apply DFunLike.ext
    intro y
    by_cases hy : y ∈ e.target <;>
      simp [tensorChartPush_apply, hy, coordinateTarget]

lemma tensorChartPull_zero (f : SupportedField (F := ComplexTensor) (chartSupport e K hK)) :
    ∀ x ∈ e.source, x ∉ (K : Set SmallModes.Base) → coordinateTarget e f x = 0 := by
  intro x hx hn
  simp only [coordinateTarget, chartPull_zero e K hK f x hx hn, map_zero]

def tensorChartPull (f : SupportedField (F := ComplexTensor) (chartSupport e K hK)) :
    SupportedField (F := ComplexTensor) K :=
  ContDiffMapSupportedIn.of_support_subset
    (contDiff_indicator_of_support e.open_source K.isCompact.isClosed hK
      (contDiffOn_coordinateTarget e.open_source f.contDiff.contDiffOn he (fun _ _ => Set.mem_univ _))
      (tensorChartPull_zero e K hK f))
    (subset_closure.trans (tsupport_indicator_subset K.isCompact.isClosed
      (tensorChartPull_zero e K hK f)))

@[simp] lemma tensorChartPull_apply (f : SupportedField (F := ComplexTensor) (chartSupport e K hK))
    (x : SmallModes.Base) :
    tensorChartPull e he K hK f x = e.source.indicator (coordinateTarget e f) x := rfl

lemma tensorChartPull_push (f : SupportedField (F := ComplexTensor) K) :
    tensorChartPull e he K hK (tensorChartPush e hi K hK f) = f := by
  apply DFunLike.ext
  intro x
  by_cases hx : x ∈ e.source
  · rw [tensorChartPull_apply, Set.indicator_of_mem hx]
    change complexPullbackField e x (tensorChartPush e hi K hK f (e x)) = f x
    rw [tensorChartPush_apply, Set.indicator_of_mem (e.map_source hx)]
    change complexPullbackField e x (complexPullbackField e.symm (e x) (f (e.symm (e x)))) = f x
    rw [e.left_inv hx]
    apply complexPullbackField_inverse
    · exact (he.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt (by simp)
    · exact (hi.contDiffAt (e.open_target.mem_nhds (e.map_source hx))).differentiableAt (by simp)
    · filter_upwards [e.open_source.mem_nhds hx] with z hz using e.left_inv hz
  · rw [tensorChartPull_apply, Set.indicator_of_notMem hx]
    exact (f.zero_on_compl (fun hk => hx (hK hk))).symm

lemma tensorChartPush_pull (f : SupportedField (F := ComplexTensor) (chartSupport e K hK)) :
    tensorChartPush e hi K hK (tensorChartPull e he K hK f) = f := by
  apply DFunLike.ext
  intro y
  by_cases hy : y ∈ e.target
  · rw [tensorChartPush_apply, Set.indicator_of_mem hy]
    change complexPullbackField e.symm y (tensorChartPull e he K hK f (e.symm y)) = f y
    rw [tensorChartPull_apply, Set.indicator_of_mem (e.map_target hy)]
    change complexPullbackField e.symm y (complexPullbackField e (e.symm y) (f (e (e.symm y)))) = f y
    rw [e.right_inv hy]
    apply complexPullbackField_inverse
    · exact (hi.contDiffAt (e.open_target.mem_nhds hy)).differentiableAt (by simp)
    · exact (he.contDiffAt (e.open_source.mem_nhds (e.map_target hy))).differentiableAt (by simp)
    · filter_upwards [e.open_target.mem_nhds hy] with z hz using e.right_inv hz
  · rw [tensorChartPush_apply, Set.indicator_of_notMem hy]
    exact (f.zero_on_compl (fun hk => hy (chartSupport_subset e K hK hk))).symm

def tensorChartEquiv :
    SupportedField (F := ComplexTensor) K ≃ₗ[ℝ] SupportedField (F := ComplexTensor) (chartSupport e K hK) where
  toFun := tensorChartPush e hi K hK
  invFun := tensorChartPull e he K hK
  left_inv := tensorChartPull_push e he hi K hK
  right_inv := tensorChartPush_pull e he hi K hK
  map_add' := (tensorChartPushLM e hi K hK).map_add
  map_smul' := (tensorChartPushLM e hi K hK).map_smul

end ClosedSurfaceR4.JetPolynomial

end

end OAI
