import OAI.Geometry.SurfaceImmersion.Atlas.TensorChartBounds

namespace OAI

/-! Supported pullback of real symmetric two-tensors. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial
open PhaseMean WeightedEstimates
variable (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiffOn ℝ ∞ e e.source) (K : Compacts SmallModes.Base)
    (hK : (K : Set SmallModes.Base) ⊆ e.source)

lemma realTensorChartPull_zero (f : SupportedField (F := Tensor) (chartSupport e K hK)) :
    ∀ x ∈ e.source, x ∉ (K : Set SmallModes.Base) → pullbackField e x (f (e x)) = 0 := by
  intro x hx hn
  rw [chartPull_zero e K hK f x hx hn, map_zero]

def realTensorChartPull (f : SupportedField (F := Tensor) (chartSupport e K hK)) :
    SupportedField (F := Tensor) K :=
  ContDiffMapSupportedIn.of_support_subset
    (contDiff_indicator_of_support e.open_source K.isCompact.isClosed hK
      (contDiffOn_pullbackField_apply e.open_source (f.contDiff.comp_contDiffOn he) he)
      (realTensorChartPull_zero e K hK f))
    (subset_closure.trans (tsupport_indicator_subset K.isCompact.isClosed
      (realTensorChartPull_zero e K hK f)))

@[simp] lemma realTensorChartPull_apply
    (f : SupportedField (F := Tensor) (chartSupport e K hK)) (x : SmallModes.Base) :
    realTensorChartPull e he K hK f x =
      e.source.indicator (fun x => pullbackField e x (f (e x))) x := rfl

lemma realTensorChartPull_sub (f g : SupportedField (F := Tensor) (chartSupport e K hK)) :
    realTensorChartPull e he K hK (f - g) =
      realTensorChartPull e he K hK f - realTensorChartPull e he K hK g := by
  apply DFunLike.ext
  intro x
  by_cases hx : x ∈ e.source <;> simp [realTensorChartPull_apply, hx, map_sub]

lemma realTensorChartPull_bound {s : ℝ≥0} {J D : ℝ} {m : ℕ}
    (hs : 0 < (s : ℝ)) (hs1 : s ≤ 1) (hJ : 1 ≤ J) (hD : 0 ≤ D)
    (hderiv : ∀ j, 1 ≤ j → j ≤ m → ∀ x ∈ e.source,
      ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ J)
    (hfield : ∀ v, ‖v‖ ≤ 1 → WeightedBound e.source s m D (SmallModes.coordDeriv v e))
    (f : SupportedField (F := Tensor) (chartSupport e K hK)) :
    supportedWeightedSeminorm K s m (realTensorChartPull e he K hK f) ≤
      tensorChartBudget m J D * supportedWeightedSeminorm (chartSupport e K hK) s m f := by
  have hN : 0 ≤ supportedWeightedSeminorm (chartSupport e K hK) s m f := apply_nonneg _ _
  have hb := ((weightedBound_of_supportedSeminorm s m f).restrict_open e.open_target).comp_coordinates
    e.open_source.uniqueDiffOn e.open_target.uniqueDiffOn hs hs1 hJ hN he
    f.contDiff.contDiffOn (fun _ hx => e.map_source hx) hderiv
  have ht := weighted_pullbackField_apply e.open_source hs (by positivity) hD
    (f.contDiff.comp_contDiffOn he) he hb hfield
  have hg := ht.indicator_of_support e.open_source K.isCompact.isClosed hK
    (by positivity) (realTensorChartPull_zero e K hK f)
  apply supportedSeminorm_le_of_weightedBound hs
    (mul_nonneg (tensorChartBudget_nonneg m (zero_le_one.trans hJ) hD) hN)
  convert hg using 1 <;> first | rfl | (unfold tensorChartBudget; ring)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
