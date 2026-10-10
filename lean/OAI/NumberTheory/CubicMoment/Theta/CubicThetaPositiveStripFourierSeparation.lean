import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCellFourierSeparation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveStripHorizontalDensity

namespace OAI

/-! Compact radial weights and the actual horizontal characters jointly
separate the literal cusp L2 space. -/
noncomputable section
open MeasureTheory Set
open scoped CompactlySupported ContDiff
namespace CubicFirstMoment
variable {ε : ℝ}
local instance cubicThetaPositiveStripFourierSeparationCountable : Countable Eisenstein :=
  cubicThetaFourierIndex.injective.countable

lemma cubicThetaPositiveStripRepresentative_fiber_memLp (hε : 0<ε) (F : CubicThetaPositiveStripL2 ε) :
    ∀ᵐ v ∂(volume : Measure ℝ).restrict (Ioi ε),
      MemLp (fun z : ℂ => cubicThetaPositiveStripRepresentative F (z,v)) 2
        ((volume : Measure ℂ).restrict cubicThetaHorizontalCell) := by
  have hi := cubicThetaPositiveStripRepresentative_sq_integrable hε F
  change Integrable (fun y : ℂ × ℝ => ‖cubicThetaPositiveStripRepresentative F y‖^2/y.2^3)
    (((volume : Measure ℂ).prod (volume : Measure ℝ)).restrict
      (cubicThetaHorizontalCell ×ˢ Ioi ε)) at hi
  rw [←Measure.prod_restrict] at hi
  filter_upwards [hi.prod_left_ae,ae_restrict_mem measurableSet_Ioi] with v hv hv2
  have hv0 : v≠0 := (hε.trans hv2).ne'
  have hm : AEStronglyMeasurable (fun z : ℂ => cubicThetaPositiveStripRepresentative F (z,v))
      ((volume : Measure ℂ).restrict cubicThetaHorizontalCell) :=
    ((cubicThetaPositiveStripRepresentative_measurable F).comp_measurable
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply (hv.mul_const (v^3)).congr
  filter_upwards with z
  field_simp

theorem cubicThetaPositiveStripFourier_separates (hε : 0<ε) (F : CubicThetaPositiveStripL2 ε)
    (hzero : ∀ (h : Eisenstein) (W : C_c(ℝ,ℂ)), (∀ v≤ε,W v=0) →
      ContDiff ℝ ∞ (W : ℝ → ℂ) →
      inner ℂ (cubicThetaPositiveStripFourierTest hε h W) F=0) : F=0 := by
  have hD : ∀ᵐ v ∂(volume : Measure ℝ),∀ h : Eisenstein,
      v∈Ioi ε → cubicThetaPositiveStripHorizontalDensity F h v=0 :=
    ae_all_iff.mpr (fun h => cubicThetaPositiveStripHorizontalDensity_zero hε F h (hzero h))
  have hfiber : ∀ᵐ v ∂(volume : Measure ℝ).restrict (Ioi ε),
      (fun z : ℂ => cubicThetaPositiveStripRepresentative F (z,v))
        =ᵐ[(volume : Measure ℂ).restrict cubicThetaHorizontalCell] 0 := by
    filter_upwards [cubicThetaPositiveStripRepresentative_fiber_memLp hε F,
      ae_restrict_of_ae hD,ae_restrict_mem measurableSet_Ioi] with v hv hD hv2
    apply cubicThetaCellFourier_separates hv
    intro h
    have he := hD h hv2
    rw [cubicThetaPositiveStripHorizontalDensity,integral_div] at he
    have hv0 : (v:ℂ)^3≠0 := pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr
      ((hε.trans hv2).ne'))
    simpa only [zero_mul] using (div_eq_iff hv0).mp he
  have hm : MeasurableSet {y : ℂ × ℝ | cubicThetaPositiveStripRepresentative F y=0} :=
    measurableSet_eq_fun (cubicThetaPositiveStripRepresentative_measurable F).measurable measurable_const
  have hj : ∀ᵐ y ∂((volume : Measure ℂ).restrict cubicThetaHorizontalCell).prod
      ((volume : Measure ℝ).restrict (Ioi ε)), cubicThetaPositiveStripRepresentative F y=0 :=
    (Measure.ae_prod_iff_ae_ae hm).mpr ((Measure.ae_ae_comm hm).mpr hfiber)
  rw [Measure.prod_restrict] at hj
  have hn : ‖F‖^2=0 := by
    calc
      _ = ∫ p in cubicThetaCuspStrip ε, ‖F p‖^2 ∂cubicThetaPointMeasure :=
        cubicTheta_l2_norm_sq_measure F
      _ = ∫ p in cubicThetaCuspStrip ε,
          ‖cubicThetaPositiveStripRepresentative F (cubicThetaPointCoordinates p)‖^2
            ∂cubicThetaPointMeasure := by
        apply integral_congr_ae
        filter_upwards with p
        rw [cubicThetaPositiveStripRepresentative_coordinates]
      _ = ∫ y in cubicThetaHorizontalCell ×ˢ Ioi ε,
          ‖cubicThetaPositiveStripRepresentative F y‖^2/y.2^3 := by
        have he := cubicThetaPointIntegral_density (cubicThetaCuspStrip_measurable ε)
          (fun y => ‖cubicThetaPositiveStripRepresentative F y‖^2)
        rw [cubicThetaCuspStrip_coordinates hε.le] at he
        exact he
      _ = 0 := integral_eq_zero_of_ae (hj.mono (fun y hy => by simp only [hy,norm_zero,zero_pow (by decide : 2≠0),zero_div,Pi.zero_apply]))
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)

end CubicFirstMoment

end

end OAI
