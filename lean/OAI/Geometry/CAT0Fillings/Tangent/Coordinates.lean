import Mathlib
import OAI.Geometry.CAT0Fillings.Gradient.HilbertAtlas

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

noncomputable def atlasParam (w : ℕ × Euc n) : X := (q.chart w.1).paramExtended w.2
def atlasDomain : Set (ℕ × Euc n) := {w | w.2 ∈ (q.chart w.1).domain}

lemma measurable_atlasParam : Measurable q.atlasParam :=
  measurable_from_prod_countable_right (fun i => (q.chart i).measurable_paramExtended)

lemma measurableSet_atlasDomain : MeasurableSet q.atlasDomain := by
  have he : q.atlasDomain = ⋃ i : ℕ, {i} ×ˢ (q.chart i).domain := by
    ext w
    simp only [atlasDomain,mem_ofPred_eq,mem_iUnion,mem_prod,mem_singleton_iff]
    constructor
    · exact fun h => ⟨w.1,rfl,h⟩
    · rintro ⟨i,hi,h⟩
      simpa only [hi] using h
  rw [he]
  exact MeasurableSet.iUnion (fun i => (measurableSet_singleton i).prod (q.chart i).borel)

lemma ae_mem_atlasDomain : ∀ᵐ w ∂q.atlasMeasure, w ∈ q.atlasDomain := by
  apply Measure.ae_sum_iff.mpr
  intro i
  apply (measurableEmbedding_prodMk_left i).ae_map_iff.mpr
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem (q.chart i).borel)

lemma measurableEmbedding_atlas : MeasurableEmbedding (fun w : q.atlasDomain => q.atlasParam w) := by
  let := q.measurableSet_atlasDomain.standardBorel
  apply (q.measurable_atlasParam.comp measurable_subtype_coe).measurableEmbedding
  rintro ⟨⟨i,z⟩,hz⟩ ⟨⟨j,w⟩,hw⟩ h
  change z ∈ (q.chart i).domain at hz
  change w ∈ (q.chart j).domain at hw
  change (q.chart i).paramExtended z = (q.chart j).paramExtended w at h
  simp only [IntegerChart.paramExtended,dite_eq_left hz,dite_eq_left hw] at h
  have hi : i = j := by
    by_contra hn
    apply Set.disjoint_left.mp (q.disjoint hn) (show (q.chart i).param ⟨z,hz⟩ ∈
      (q.chart i).image from ⟨⟨z,hz⟩,rfl⟩)
    rw [h]
    exact ⟨⟨w,hw⟩,rfl⟩
  subst j
  have he := congrArg Subtype.val ((q.chart i).measurableEmbedding_param.injective h)
  change z = w at he
  subst w
  rfl

lemma map_atlasMeasure : q.atlasMeasure.map q.atlasParam = MassMeasure.currentMassMeasure hT := by
  rw [atlasMeasure,Measure.map_sum q.measurable_atlasParam.aemeasurable, q.measure_eq]
  congr 1
  funext i
  rw [Measure.map_map q.measurable_atlasParam measurable_prodMk_left]
  rfl

end CAT0Fillings.ChartGeometry
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)
lemma map_coordinateMeasure_le (i : ℕ) :
    (q.coordinateMeasure i).map (q.chart i).paramExtended ≤ MassMeasure.currentMassMeasure hT := by
  rw [q.measure_eq]
  exact Measure.le_sum (fun index =>
    (q.coordinateMeasure index).map (q.chart index).paramExtended) i
lemma lintegral_coordinate_le (i : ℕ) (F : X → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z in (q.chart i).domain, ENNReal.ofReal (q.density i z)*F ((q.chart i).paramExtended z)) ≤
      ∫⁻ x, F x ∂MassMeasure.currentMassMeasure hT := by
  have h := lintegral_mono' (q.map_coordinateMeasure_le i) (le_refl F)
  rw [lintegral_map hF (q.chart i).measurable_paramExtended] at h
  rw [coordinateMeasure,lintegral_withDensity_eq_lintegral_mul₀
    (q.density_integrable i).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (show AEMeasurable (fun z => F ((q.chart i).paramExtended z)) (volume.restrict (q.chart i).domain) from
      (hF.comp (q.chart i).measurable_paramExtended).aemeasurable)] at h
  exact h
end CAT0Fillings.ChartGeometry
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.TangentDensity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  (μ : Measure E) [μ.IsAddHaarMeasure]
lemma lintegral_affine (f : E → ℝ≥0∞) (z : E) {ε : ℝ} (hε : 0 < ε) :
    (∫⁻ h, f (z+ε • h) ∂μ) =
      ENNReal.ofReal ((ε^Module.finrank ℝ E)⁻¹) * ∫⁻ x, f x ∂μ := by
  have hs := lintegral_map_equiv (μ := μ) (fun x => f (z+x))
    (Homeomorph.smul (Units.mk0 ε hε.ne')).toMeasurableEquiv
  change (∫⁻ x, f (z+x) ∂μ.map (fun h => ε • h)) = (∫⁻ h, f (z+ε • h) ∂μ) at hs
  rw [←hs,Measure.map_addHaar_smul μ hε.ne',lintegral_smul_measure,
    abs_of_pos (inv_pos.mpr (pow_pos hε _))]
  congr 1
  exact (measurePreserving_add_left μ z).lintegral_comp_emb
    (Homeomorph.addLeft z).measurableEmbedding f
end CAT0Fillings.TangentDensity
end

end OAI
