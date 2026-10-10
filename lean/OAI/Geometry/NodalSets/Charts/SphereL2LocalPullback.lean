import OAI.Geometry.NodalSets.Charts.SphereChartEnergyBounds
import OAI.Geometry.NodalSets.Charts.SphereWeightedChartL2

namespace OAI

namespace Yau.Target
open MeasureTheory Set Yau.Geometry
noncomputable section
local instance sphereL2LocalPullbackMeasurable : MeasurableSpace Base := borel Base
local instance sphereL2LocalPullbackBorel : BorelSpace Base := ⟨rfl⟩

theorem sphereWeightedL2_chart_aestronglyMeasurable (d : SphereEnergyData)
    (f : SphereWeightedL2 d) (p : Base) : AEStronglyMeasurable (fun x ↦ f (sphereChartCoordMap p x)) := by
  have hr : sphereReferenceMeasure ≪ sphereWeightedMeasure d.density :=
    withDensity_absolutelyContinuous' d.continuous.measurable.ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall (fun x ↦ (ENNReal.ofReal_pos.mpr (d.positive x)).ne'))
  have hf := AEStronglyMeasurable.mono_ac hr (Lp.aestronglyMeasurable f)
  rw [sphereReferenceMeasure_eq_chart p,
    (sphereChartCoordMap_measurableEmbedding p).aestronglyMeasurable_map_iff] at hf
  simp only [roundChartDensity_coord_eq] at hf
  exact AEStronglyMeasurable.mono_ac
    (withDensity_absolutelyContinuous' roundCoordDensity_smooth.continuous.measurable.ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall (fun x ↦ (ENNReal.ofReal_pos.mpr (roundCoordDensity_pos x)).ne'))) hf

theorem sphereWeightedL2_norm_sq_integral (d : SphereEnergyData) (f : SphereWeightedL2 d) :
    ‖f‖^2 = ∫ x, d.density x*(f x)^2 ∂sphereReferenceMeasure := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def,
    sphereWeightedMeasure_integral d.density d.continuous (fun x ↦ (d.positive x).le)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x ↦ by
    simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs])

theorem sphereWeightedL2_compact_chart_bound (d : SphereEnergyData) (p : Base)
    {K : Set Yau.Jets.Coord} (hK : IsCompact K) :
    ∃ C > 0, ∀ f : SphereWeightedL2 d,
      MemLp (fun x ↦ f (sphereChartCoordMap p x)) 2 (volume.restrict K) ∧
      (∫ x in K, (f (sphereChartCoordMap p x))^2) ≤ C*‖f‖^2 := by
  let a := fun x ↦ roundCoordDensity x*d.density (sphereChartCoordMap p x)
  obtain ⟨q,hq,_,_,hqb⟩ := Yau.Jets.compact_positive_bounds hK a
    ((roundCoordDensity_smooth.continuous.mul
      (d.continuous.comp (sphereChartCoordMap_smooth p).continuous)).continuousOn)
    (fun x _ ↦ mul_pos (roundCoordDensity_pos x) (d.positive _))
  refine ⟨q⁻¹,inv_pos.mpr hq,?_⟩
  intro f
  have hf := sphereWeightedL2_chart_aestronglyMeasurable d f p
  have hs := (Lp.memLp f).integrable_sq
  have hi : Integrable (fun x ↦ a x*(f (sphereChartCoordMap p x))^2) := by
    have h := (sphereReferenceMeasure_integrable_chart p _).mp
      ((sphereWeightedMeasure_integrable_iff d _).mp hs)
    simpa only [roundChartDensity_coord_eq,a,mul_assoc] using h
  have hbound : ∀ x ∈ K, (f (sphereChartCoordMap p x))^2 ≤ q⁻¹*(a x*(f (sphereChartCoordMap p x))^2) := by
    intro x hx
    have h := mul_le_mul_of_nonneg_right (hqb x hx).1 (sq_nonneg (f (sphereChartCoordMap p x)))
    calc
      _ = q⁻¹*(q*(f (sphereChartCoordMap p x))^2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hq.le)
  have his : IntegrableOn (fun x ↦ (f (sphereChartCoordMap p x))^2) K := by
    apply ((hi.const_mul q⁻¹).integrableOn).mono' (hf.pow 2).restrict
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    change |(f (sphereChartCoordMap p x))^2| ≤ _
    rw [abs_of_nonneg (sq_nonneg _)]
    exact hbound x hx
  refine ⟨(memLp_two_iff_integrable_sq hf.restrict).mpr his,?_⟩
  calc
    _ ≤ ∫ x in K, q⁻¹*(a x*(f (sphereChartCoordMap p x))^2) :=
      setIntegral_mono_on his (hi.const_mul q⁻¹).integrableOn hK.measurableSet hbound
    _ ≤ ∫ x, q⁻¹*(a x*(f (sphereChartCoordMap p x))^2) :=
      setIntegral_le_integral (hi.const_mul q⁻¹) (Filter.Eventually.of_forall (fun x ↦ by
        exact mul_nonneg (inv_nonneg.mpr hq.le)
          (mul_nonneg (mul_pos (roundCoordDensity_pos x) (d.positive _)).le (sq_nonneg _))))
    _ = _ := by
      rw [integral_const_mul,sphereWeightedL2_norm_sq_integral,sphereReferenceMeasure_integral_chart p]
      simp only [roundChartDensity_coord_eq,a,mul_assoc]

end
end Yau.Target

end OAI
