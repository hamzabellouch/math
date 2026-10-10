import OAI.Analysis.FiniteFactor.OrbitSampling.CompactTorus

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Classical
noncomputable section

abbrev SourceTorus := SourceCoordinate → UnitAddCircle
abbrev sourceTorusHaar : Measure SourceTorus :=
  Measure.infinitePi (fun _ : SourceCoordinate => (volume : Measure UnitAddCircle))

instance sourceUnitCircle_probability : IsProbabilityMeasure (volume : Measure UnitAddCircle) := by
  rw [← sourceCircle_mk_preserving.map_eq]
  infer_instance

def sourceTorusQuotient (x : SourceCoordinate → ℝ) : SourceTorus := fun i => (x i : UnitAddCircle)
def sourceTorusRepresentative (z : SourceTorus) : SourceCoordinate → ℝ :=
  fun i => sourceCircleRepresentative (z i)

theorem sourceTorusQuotient_preserving : MeasurePreserving sourceTorusQuotient sourceSamplingHaar sourceTorusHaar := by
  refine ⟨Measurable.of_eval (fun i => sourceCircle_mk_preserving.measurable.comp (measurable_pi_apply i)),?_⟩
  unfold sourceTorusQuotient
  rw [Measure.infinitePi_map_pi _ (fun _ => sourceCircle_mk_preserving.measurable)]
  simp only [sourceCircle_mk_preserving.map_eq]

theorem sourceTorusRepresentative_preserving :
    MeasurePreserving sourceTorusRepresentative sourceTorusHaar sourceSamplingHaar := by
  refine ⟨Measurable.of_eval (fun i => sourceCircleRepresentative_measurable.comp (measurable_pi_apply i)),?_⟩
  unfold sourceTorusRepresentative
  rw [Measure.infinitePi_map_pi _ (fun _ => sourceCircleRepresentative_measurable)]
  simp only [sourceCircleRepresentative_preserving.map_eq]

theorem sourceTorusRepresentative_cube (z : SourceTorus) :
    ∀ i, sourceTorusRepresentative z i ∈ Set.Ico (0 : ℝ) 1 := by
  intro i
  change ((AddCircle.equivIco 1 0) (z i)).val ∈ Set.Ico (0 : ℝ) 1
  simpa only [zero_add] using (AddCircle.equivIco 1 0 (z i)).property

theorem sourceTorusRepresentative_quotient (x : SourceCoordinate → ℝ)
    (hx : ∀ i, x i ∈ Set.Ico (0 : ℝ) 1) :
    sourceTorusRepresentative (sourceTorusQuotient x) = x := by
  funext i
  exact (sourceCircleRepresentative_coe (x i)).trans (Int.fract_eq_self.mpr (hx i))

theorem sourceTorusQuotient_representative (z : SourceTorus) :
    sourceTorusQuotient (sourceTorusRepresentative z) = z := by
  funext i
  exact (AddCircle.equivIco 1 0).symm_apply_apply (z i)

/-- Change of variables for actual weighted laws across the real
representatives and compact torus, with the inverse needed only almost everywhere. -/
theorem sourceTorusQuotient_withDensity (w : (SourceCoordinate → ℝ) → ℝ≥0∞) (hw : Measurable w) :
    (sourceSamplingHaar.withDensity w).map sourceTorusQuotient =
      sourceTorusHaar.withDensity (fun z => w (sourceTorusRepresentative z)) := by
  ext A hA
  have hQ := sourceTorusQuotient_preserving
  have hR := sourceTorusRepresentative_preserving
  rw [Measure.map_apply hQ.measurable hA,withDensity_apply _ (hQ.measurable hA),withDensity_apply _ hA,
    ← lintegral_indicator (hQ.measurable hA),← lintegral_indicator hA]
  have hm := (hw.comp hR.measurable).indicator hA
  calc
    _ = ∫⁻ x, A.indicator (fun z => w (sourceTorusRepresentative z)) (sourceTorusQuotient x) ∂sourceSamplingHaar := by
      apply lintegral_congr_ae
      filter_upwards [sourceSamplingHaar_cube] with x hx
      change (if sourceTorusQuotient x ∈ A then w x else 0) =
        (if sourceTorusQuotient x ∈ A then w (sourceTorusRepresentative (sourceTorusQuotient x)) else 0)
      rw [sourceTorusRepresentative_quotient x hx]
    _ = _ := hQ.lintegral_comp hm

end
end FiniteFactor

end OAI
