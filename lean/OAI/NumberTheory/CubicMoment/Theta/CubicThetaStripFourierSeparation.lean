import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCellFourierSeparation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaStripHorizontalDensity

namespace OAI

/-! Compact radial weights and the actual horizontal characters jointly
separate the literal cusp L2 space. -/
noncomputable section
open MeasureTheory Set
open scoped CompactlySupported
namespace CubicFirstMoment
local instance cubicThetaStripFourierSeparationCountable : Countable Eisenstein :=
  cubicThetaFourierIndex.injective.countable

lemma cubicThetaStripRepresentative_fiber_memLp (F : CubicThetaStripL2) :
    ∀ᵐ v ∂(volume : Measure ℝ).restrict (Ioi (2:ℝ)),
      MemLp (fun z : ℂ => cubicThetaStripRepresentative F (z,v)) 2
        ((volume : Measure ℂ).restrict cubicThetaHorizontalCell) := by
  have hi := cubicThetaStripRepresentative_sq_integrable F
  change Integrable (fun y : ℂ × ℝ => ‖cubicThetaStripRepresentative F y‖^2/y.2^3)
    (((volume : Measure ℂ).prod (volume : Measure ℝ)).restrict
      (cubicThetaHorizontalCell ×ˢ Ioi (2:ℝ))) at hi
  rw [←Measure.prod_restrict] at hi
  filter_upwards [hi.prod_left_ae,ae_restrict_mem measurableSet_Ioi] with v hv hv2
  have hv0 : v≠0 := by have h : 2<v := hv2; linarith
  have hm : AEStronglyMeasurable (fun z : ℂ => cubicThetaStripRepresentative F (z,v))
      ((volume : Measure ℂ).restrict cubicThetaHorizontalCell) :=
    ((cubicThetaStripRepresentative_measurable F).comp_measurable
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply (hv.mul_const (v^3)).congr
  filter_upwards with z
  field_simp

theorem cubicThetaStripFourier_separates (F : CubicThetaStripL2)
    (hzero : ∀ (h : Eisenstein) (W : C_c(ℝ,ℂ)), (∀ v≤(2:ℝ),W v=0) →
      inner ℂ (cubicThetaCuspFourierTest h W) F=0) : F=0 := by
  have hD : ∀ᵐ v ∂(volume : Measure ℝ),∀ h : Eisenstein,
      v∈Ioi (2:ℝ) → cubicThetaStripHorizontalDensity F h v=0 :=
    ae_all_iff.mpr (fun h => cubicThetaStripHorizontalDensity_zero F h (hzero h))
  have hfiber : ∀ᵐ v ∂(volume : Measure ℝ).restrict (Ioi (2:ℝ)),
      (fun z : ℂ => cubicThetaStripRepresentative F (z,v))
        =ᵐ[(volume : Measure ℂ).restrict cubicThetaHorizontalCell] 0 := by
    filter_upwards [cubicThetaStripRepresentative_fiber_memLp F,
      ae_restrict_of_ae hD,ae_restrict_mem measurableSet_Ioi] with v hv hD hv2
    apply cubicThetaCellFourier_separates hv
    intro h
    have he := hD h hv2
    rw [cubicThetaStripHorizontalDensity,integral_div] at he
    have hv0 : (v:ℂ)^3≠0 := pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr
      (by have h : 2<v := hv2; linarith))
    simpa only [zero_mul] using (div_eq_iff hv0).mp he
  have hm : MeasurableSet {y : ℂ × ℝ | cubicThetaStripRepresentative F y=0} :=
    measurableSet_eq_fun (cubicThetaStripRepresentative_measurable F).measurable measurable_const
  have hj : ∀ᵐ y ∂((volume : Measure ℂ).restrict cubicThetaHorizontalCell).prod
      ((volume : Measure ℝ).restrict (Ioi (2:ℝ))), cubicThetaStripRepresentative F y=0 :=
    (Measure.ae_prod_iff_ae_ae hm).mpr ((Measure.ae_ae_comm hm).mpr hfiber)
  rw [Measure.prod_restrict] at hj
  have hn : ‖F‖^2=0 := by
    calc
      _ = ∫ p in cubicThetaCuspStrip 2, ‖F p‖^2 ∂cubicThetaPointMeasure :=
        cubicTheta_l2_norm_sq_measure F
      _ = ∫ p in cubicThetaCuspStrip 2,
          ‖cubicThetaStripRepresentative F (cubicThetaPointCoordinates p)‖^2
            ∂cubicThetaPointMeasure := by
        apply integral_congr_ae
        filter_upwards with p
        rw [cubicThetaStripRepresentative_coordinates]
      _ = ∫ y in cubicThetaHorizontalCell ×ˢ Ioi (2:ℝ),
          ‖cubicThetaStripRepresentative F y‖^2/y.2^3 := by
        have he := cubicThetaPointIntegral_density (cubicThetaCuspStrip_measurable 2)
          (fun y => ‖cubicThetaStripRepresentative F y‖^2)
        rw [cubicThetaCuspStrip_coordinates (by norm_num : (0:ℝ)≤2)] at he
        exact he
      _ = 0 := integral_eq_zero_of_ae (hj.mono (fun y hy => by simp only [hy,norm_zero,zero_pow (by decide : 2≠0),zero_div,Pi.zero_apply]))
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)

end CubicFirstMoment

end

end OAI
