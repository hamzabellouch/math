import OAI.MeasureTheory.Falconer.Slicing.GaussianPointClose
import OAI.MeasureTheory.Falconer.Slicing.GaussianCloseMass

namespace OAI

/-! # Incidence averaging for the original point and direction labels -/

namespace Falconer
open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

theorem gaussian_point_band_label_average
    (ξ : Measure (Space d × Sphere d)) [SFinite ξ]
    (A : Fin h → Space d) {r : ℝ} (hr : 0 ≤ r) :
    (∫⁻ z : Space h, ξ {t | t.1 ∈ gaussianPointBand A z r}) =
      ENNReal.ofReal ((2*r)^h)*ξ univ := by
  let S : Set (Space h × (Space d × Sphere d)) := {p | p.2.1 ∈ gaussianPointBand A p.1 r}
  have hS : MeasurableSet S := by
    change MeasurableSet {p : Space h × (Space d × Sphere d) |
      ∀ i, |inner ℝ p.2.1 (A i)-p.1 i| ≤ r}
    simp only [ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (by fun_prop) measurable_const
  calc
    _ = ((volume : Measure (Space h)).prod ξ) S := (Measure.prod_apply hS).symm
    _ = ∫⁻ t : Space d × Sphere d, (volume : Measure (Space h))
        {z | t.1 ∈ gaussianPointBand A z r} ∂ξ := Measure.prod_apply_symm hS
    _ = ∫⁻ _ : Space d × Sphere d, ENNReal.ofReal ((2*r)^h) ∂ξ := by
      apply lintegral_congr
      intro t
      exact gaussianPointBand_parameter_measure A t.1 hr
    _ = _ := lintegral_const _

theorem gaussian_incidence_raw_point_average
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set (Space d × Sphere d)) (_hE : MeasurableSet E)
    (A : Fin h → Space d) {r : ℝ} (hr : 0 ≤ r) :
    (∫⁻ z : Space h, (μ.prod ν) (E ∩ ((gaussianPointBand A z r) ×ˢ (gaussianDirectionBand A r)))) =
      ENNReal.ofReal ((2*r)^h)*(μ.prod ν) (E ∩ (univ ×ˢ (gaussianDirectionBand A r))) := by
  let F := E ∩ (univ ×ˢ (gaussianDirectionBand A r))
  have hh := gaussian_point_band_label_average ((μ.prod ν).restrict F) A hr
  have he (z : Space h) : ((μ.prod ν).restrict F) {t | t.1 ∈ gaussianPointBand A z r} =
      (μ.prod ν) (E ∩ ((gaussianPointBand A z r) ×ˢ (gaussianDirectionBand A r))) := by
    rw [Measure.restrict_apply (show MeasurableSet {t : Space d × Sphere d |
      t.1 ∈ gaussianPointBand A z r} from
        (gaussianPointBand_measurable A z r).preimage measurable_fst)]
    congr 1
    ext t
    simp only [F,mem_inter_iff,mem_prod,mem_univ,mem_ofPred_eq,true_and]
    tauto
  simpa only [he,Measure.restrict_apply_univ,F] using hh

theorem gaussian_slice_incidence_point_average
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    (A : Fin h → Space d) {r : ℝ} (hr : 0 < r) :
    (∫⁻ z : Space h, (gaussianPointSliceMeasure μ A z r).prod
      (gaussianDirectionSliceMeasure ν A r) E) =
      ENNReal.ofReal ((2:ℝ)^h)*
        gaussianDirectionMass (((μ.prod ν).restrict E).map Prod.snd) r A := by
  have he (z : Space h) : (gaussianPointSliceMeasure μ A z r).prod
      (gaussianDirectionSliceMeasure ν A r) E =
      (ENNReal.ofReal (r^(-(h:ℝ))))^2*
        (μ.prod ν) (E ∩ ((gaussianPointBand A z r) ×ˢ (gaussianDirectionBand A r))) := by
    simp only [gaussianPointSliceMeasure,gaussianDirectionSliceMeasure,Measure.prod_smul_left,
      Measure.prod_smul_right,Measure.smul_apply,smul_eq_mul,Measure.prod_restrict,
      Measure.restrict_apply hE,pow_two,mul_assoc]
  simp_rw [he]
  rw [lintegral_const_mul' _ _ (by
    rw [pow_two]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
    gaussian_incidence_raw_point_average μ ν E hE A hr.le]
  have hmap : (((μ.prod ν).restrict E).map Prod.snd) (gaussianDirectionBand A r) =
      (μ.prod ν) (E ∩ (univ ×ˢ (gaussianDirectionBand A r))) := by
    rw [Measure.map_apply measurable_snd (gaussianDirectionBand_measurable A r),
      Measure.restrict_apply ((gaussianDirectionBand_measurable A r).preimage measurable_snd)]
    congr 1
    ext t
    simp only [mem_inter_iff,mem_preimage,mem_prod,mem_univ,true_and]
    tauto
  rw [gaussianDirectionMass,hmap,pow_two]
  calc
    _ = (ENNReal.ofReal (r^(-(h:ℝ)))*ENNReal.ofReal ((2*r)^h))*
        (ENNReal.ofReal (r^(-(h:ℝ)))*(μ.prod ν) (E ∩ (univ ×ˢ gaussianDirectionBand A r))) := by ac_rfl
    _ = _ := by rw [gaussian_band_normalization hr (by norm_num : (0:ℝ) ≤ 2)]

theorem gaussian_slice_incidence_mean_lower
    (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set (Space d × Sphere d)) (hE : MeasurableSet E)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ENNReal.ofReal ((2:ℝ)^h)*ENNReal.ofReal (gaussianBandLowerConstant^h)*(μ.prod ν) E ≤
      ∫⁻ A : Fin h → Space d, (∫⁻ z : Space h,
        (gaussianPointSliceMeasure μ A z r).prod (gaussianDirectionSliceMeasure ν A r) E) ∂gaussianRows d h := by
  simp_rw [gaussian_slice_incidence_point_average μ ν E hE _ hr]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hh := gaussian_direction_mass_mean_lower (h := h) (((μ.prod ν).restrict E).map Prod.snd) hr hr1
  rw [Measure.map_apply measurable_snd MeasurableSet.univ,preimage_univ,Measure.restrict_apply_univ] at hh
  simpa only [mul_assoc] using mul_le_mul_right hh (ENNReal.ofReal ((2:ℝ)^h))

end Falconer

end OAI
