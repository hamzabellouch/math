import OAI.Geometry.SurfaceImmersion.Atlas.SupportedTensorChart

namespace OAI

/-! Weighted estimates for tensor transport through phase charts. The
change of chart changes constants but introduces no scale loss. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates PhaseMean

variable (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (K : Compacts SmallModes.Base) (hK : (K : Set SmallModes.Base) ⊆ e.source)

def tensorChartBudget (m : ℕ) (J D : ℝ) : ℝ :=
  4 * (2 ^ m * (2 ^ m * ((m.factorial : ℝ) * J ^ m) * D) * D)

lemma tensorChartBudget_nonneg (m : ℕ) {J D : ℝ} (hJ : 0 ≤ J) (hD : 0 ≤ D) :
    0 ≤ tensorChartBudget m J D := by unfold tensorChartBudget; positivity

lemma tensorChartPush_bound (hi : ContDiffOn ℝ ∞ e.symm e.target)
    {s : ℝ≥0} {J D : ℝ} {m : ℕ} (hs : 0 < (s : ℝ)) (hs1 : s ≤ 1)
    (hJ : 1 ≤ J) (hD : 0 ≤ D)
    (hderiv : ∀ j, 1 ≤ j → j ≤ m → ∀ y ∈ e.target,
      ‖iteratedFDerivWithin ℝ j e.symm e.target y‖ ≤ J)
    (hfield : ∀ v, ‖v‖ ≤ 1 → WeightedBound e.target s m D
      (SmallModes.coordDeriv v e.symm)) (f : SupportedField (F := ComplexTensor) K) :
    supportedWeightedSeminorm (chartSupport e K hK) s m (tensorChartPush e hi K hK f) ≤
      tensorChartBudget m J D * supportedWeightedSeminorm K s m f := by
  have hN : 0 ≤ supportedWeightedSeminorm K s m f := apply_nonneg _ _
  have hb := ((weightedBound_of_supportedSeminorm s m f).restrict_open e.open_source).comp_coordinates
    e.open_target.uniqueDiffOn e.open_source.uniqueDiffOn hs hs1 hJ hN hi
    f.contDiff.contDiffOn (fun _ hy => e.map_target hy) hderiv
  have ht := weighted_complexPullbackField_apply e.open_target hs (by positivity) hD
    (f.contDiff.comp_contDiffOn hi) hi hb hfield
  have hg := ht.indicator_of_support e.open_target (chartSupport e K hK).isCompact.isClosed
    (chartSupport_subset e K hK) (by positivity) (tensorChartPush_zero e K hK f)
  apply supportedSeminorm_le_of_weightedBound hs
    (mul_nonneg (tensorChartBudget_nonneg m (zero_le_one.trans hJ) hD) hN)
  convert hg using 1 <;> first | rfl | (unfold tensorChartBudget; ring)

lemma tensorChartPull_bound (he : ContDiffOn ℝ ∞ e e.source)
    {s : ℝ≥0} {J D : ℝ} {m : ℕ} (hs : 0 < (s : ℝ)) (hs1 : s ≤ 1)
    (hJ : 1 ≤ J) (hD : 0 ≤ D)
    (hderiv : ∀ j, 1 ≤ j → j ≤ m → ∀ x ∈ e.source,
      ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ J)
    (hfield : ∀ v, ‖v‖ ≤ 1 → WeightedBound e.source s m D
      (SmallModes.coordDeriv v e)) (f : SupportedField (F := ComplexTensor) (chartSupport e K hK)) :
    supportedWeightedSeminorm K s m (tensorChartPull e he K hK f) ≤
      tensorChartBudget m J D * supportedWeightedSeminorm (chartSupport e K hK) s m f := by
  have hN : 0 ≤ supportedWeightedSeminorm (chartSupport e K hK) s m f := apply_nonneg _ _
  have hb := ((weightedBound_of_supportedSeminorm s m f).restrict_open e.open_target).comp_coordinates
    e.open_source.uniqueDiffOn e.open_target.uniqueDiffOn hs hs1 hJ hN he
    f.contDiff.contDiffOn (fun _ hx => e.map_source hx) hderiv
  have ht := weighted_complexPullbackField_apply e.open_source hs (by positivity) hD
    (f.contDiff.comp_contDiffOn he) he hb hfield
  have hg := ht.indicator_of_support e.open_source K.isCompact.isClosed hK
    (by positivity) (tensorChartPull_zero e K hK f)
  apply supportedSeminorm_le_of_weightedBound hs
    (mul_nonneg (tensorChartBudget_nonneg m (zero_le_one.trans hJ) hD) hN)
  convert hg using 1 <;> first | rfl | (unfold tensorChartBudget; ring)

def chartTensorTransportLM (he : ContDiffOn ℝ ∞ e e.source)
    (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (R : SupportedField (F := Fin 4 → ℂ) K →ₗ[ℝ] SupportedField (F := ComplexTensor) K) :
    SupportedField (F := Fin 4 → ℂ) (chartSupport e K hK) →ₗ[ℝ]
      SupportedField (F := ComplexTensor) (chartSupport e K hK) :=
  (tensorChartEquiv e he hi K hK).toLinearMap.comp
    (R.comp (chartEquiv e he hi K hK).symm.toLinearMap)

lemma chartTensorTransportLM_bound (he : ContDiffOn ℝ ∞ e e.source)
    (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (R : SupportedField (F := Fin 4 → ℂ) K →ₗ[ℝ] SupportedField (F := ComplexTensor) K)
    {s : ℝ≥0} {J I D C : ℝ} {m r : ℕ} (hs : 0 < (s : ℝ)) (hs1 : s ≤ 1)
    (hJ : 1 ≤ J) (hI : 1 ≤ I) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hebound : ∀ j, 1 ≤ j → j ≤ r → ∀ x ∈ e.source,
      ‖iteratedFDerivWithin ℝ j e e.source x‖ ≤ J)
    (hibound : ∀ j, 1 ≤ j → j ≤ m → ∀ x ∈ e.target,
      ‖iteratedFDerivWithin ℝ j e.symm e.target x‖ ≤ I)
    (hfield : ∀ v, ‖v‖ ≤ 1 → WeightedBound e.target s m D
      (SmallModes.coordDeriv v e.symm))
    (hR : ∀ f, supportedWeightedSeminorm K s m (R f) ≤ C * supportedWeightedSeminorm K s r f)
    (f : SupportedField (F := Fin 4 → ℂ) (chartSupport e K hK)) :
    supportedWeightedSeminorm (chartSupport e K hK) s m (chartTensorTransportLM e K hK he hi R f) ≤
      (tensorChartBudget m I D * C * ((r.factorial : ℝ) * J ^ r)) *
        supportedWeightedSeminorm (chartSupport e K hK) s r f := by
  have hbudget := tensorChartBudget_nonneg m (zero_le_one.trans hI) hD
  have hpush := tensorChartPush_bound e K hK hi hs hs1 hI hD hibound hfield (R (chartPull e he K hK f))
  have hpull := chartPull_bound e he K hK hs hs1 hJ hebound f
  change supportedWeightedSeminorm _ s m (tensorChartPush e hi K hK (R (chartPull e he K hK f))) ≤ _
  calc
    _ ≤ tensorChartBudget m I D * (C * supportedWeightedSeminorm K s r (chartPull e he K hK f)) :=
      hpush.trans (mul_le_mul_of_nonneg_left (hR _) hbudget)
    _ ≤ tensorChartBudget m I D * (C * ((r.factorial : ℝ) *
        supportedWeightedSeminorm (chartSupport e K hK) s r f * J ^ r)) := by gcongr
    _ = _ := by ring

end ClosedSurfaceR4.JetPolynomial

end

end OAI
