import OAI.Geometry.NodalSets.Charts.SphereL2LocalPullback

namespace OAI

namespace Yau.Target
open MeasureTheory Set Yau.Geometry
noncomputable section
local instance sphereUniformChartMeasurable : MeasurableSpace Base := borel Base
local instance sphereUniformChartBorel : BorelSpace Base := ⟨rfl⟩

theorem sphereWeightedL2_chart_bound_of_lower (d : SphereEnergyData) (p : Base)
    {K : Set Yau.Jets.Coord} (hK : IsCompact K) (q : ℝ) (hq : 0 < q)
    (hlow : ∀ x ∈ K, q ≤ roundCoordDensity x*d.density (sphereChartCoordMap p x))
    (f : SphereWeightedL2 d) :
    MemLp (fun x ↦ f (sphereChartCoordMap p x)) 2 (volume.restrict K) ∧
      (∫ x in K, (f (sphereChartCoordMap p x))^2) ≤ q⁻¹*‖f‖^2 := by
  let a := fun x ↦ roundCoordDensity x*d.density (sphereChartCoordMap p x)
  have hf := sphereWeightedL2_chart_aestronglyMeasurable d f p
  have hs := (Lp.memLp f).integrable_sq
  have hi : Integrable (fun x ↦ a x*(f (sphereChartCoordMap p x))^2) := by
    have h := (sphereReferenceMeasure_integrable_chart p _).mp
      ((sphereWeightedMeasure_integrable_iff d _).mp hs)
    simpa only [roundChartDensity_coord_eq,a,mul_assoc] using h
  have hbound : ∀ x ∈ K, (f (sphereChartCoordMap p x))^2 ≤ q⁻¹*(a x*(f (sphereChartCoordMap p x))^2) := by
    intro x hx
    have h := mul_le_mul_of_nonneg_right (hlow x hx) (sq_nonneg (f (sphereChartCoordMap p x)))
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

theorem sphereWeightedL2_chart_neighborhood (d₀ : SphereEnergyData) (p : Base)
    {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q) :
    ∃ eps > 0, ∃ K > 0, ∀ d : SphereEnergyData,
      (∀ x ∈ Q, |roundCoordDensity x*d.density (sphereChartCoordMap p x)-
        roundCoordDensity x*d₀.density (sphereChartCoordMap p x)| ≤ eps) →
      ∀ f : SphereWeightedL2 d,
        MemLp (fun x ↦ f (sphereChartCoordMap p x)) 2 (volume.restrict Q) ∧
        (∫ x in Q, (f (sphereChartCoordMap p x))^2) ≤ K*‖f‖^2 := by
  obtain ⟨q,hq,_,_,hb⟩ := Yau.Jets.compact_positive_bounds hQ
    (fun x ↦ roundCoordDensity x*d₀.density (sphereChartCoordMap p x))
    ((roundCoordDensity_smooth.continuous.mul
      (d₀.continuous.comp (sphereChartCoordMap_smooth p).continuous)).continuousOn)
    (fun x _ ↦ mul_pos (roundCoordDensity_pos x) (d₀.positive _))
  refine ⟨q/2,by positivity,(q/2)⁻¹,by positivity,fun d hclose f ↦ ?_⟩
  apply sphereWeightedL2_chart_bound_of_lower d p hQ (q/2) (by positivity) _ f
  intro x hx
  have h := (abs_le.mp (hclose x hx)).1
  have hbase := (hb x hx).1
  linarith

end
end Yau.Target

end OAI
