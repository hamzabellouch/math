import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarHeatKernel
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay

namespace OAI

/-! Construction of the actual positive finite-smooth planar resolvent mode.
Tonelli/Fubini give an L¹ resolvent kernel of mass one, so convolution with
the manuscript's compact forcing has C⁷ regularity. The resolvent differential
equation, quantitative tails and excitation gap are subsequent steps. -/

noncomputable section
open MeasureTheory Function
open scoped Convolution
namespace ContinuumCoulomb

def planarResolventIntegrand (p : ℝ × PlanarPosition) : ℝ :=
  Real.exp (-p.1) * planarHeatKernel p.1 p.2

theorem planarResolventIntegrand_measurable : Measurable planarResolventIntegrand := by
  unfold planarResolventIntegrand planarHeatKernel
  fun_prop

theorem planarResolventIntegrand_integrable :
    Integrable planarResolventIntegrand
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume : Measure PlanarPosition)) := by
  apply (integrable_prod_iff planarResolventIntegrand_measurable.aestronglyMeasurable).mpr
  have hE : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Set.Ioi (0 : ℝ)) := by
    simpa only [neg_mul, one_mul] using exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1)
  refine ⟨?_, hE.congr ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (planarHeatKernel_integrable ht).const_mul (Real.exp (-t))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hn (r : PlanarPosition) : ‖planarResolventIntegrand (t, r)‖ =
        Real.exp (-t) * planarHeatKernel t r := by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · rfl
      · exact mul_nonneg (Real.exp_pos _).le (planarHeatKernel_positive ht r).le
    simp_rw [hn]
    rw [integral_const_mul, planarHeatKernel_integral ht, mul_one]

def planarResolventKernel (r : PlanarPosition) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), planarResolventIntegrand (t, r)

theorem planarResolventKernel_integrable : Integrable planarResolventKernel :=
  planarResolventIntegrand_integrable.integral_prod_right

theorem planarResolvent_forcing_integrable (r : PlanarPosition) :
    Integrable (fun p : ℝ × PlanarPosition => planarResolventIntegrand p * planarForcing (r - p.2))
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume : Measure PlanarPosition)) := by
  apply planarResolventIntegrand_integrable.mul_bdd
    ((planarForcing_C7.continuous.comp (continuous_const.sub continuous_snd)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun p => by
    change ‖planarForcing (r - p.2)‖ ≤ (1 : ℝ)
    rw [Real.norm_eq_abs, abs_of_nonneg (planarForcing_nonnegative _)]
    exact planarForcing_le_one _)

def planarResolventMode (r : PlanarPosition) : ℝ :=
  ∫ b, planarResolventKernel b * planarForcing (r - b)

theorem planarResolventMode_C7 : ContDiff ℝ 7 planarResolventMode :=
  planarForcing_hasCompactSupport.contDiff_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ) planarResolventKernel_integrable.locallyIntegrable planarForcing_C7

/-- This is exactly the Gaussian heat representation in the manuscript. -/
theorem planarResolventMode_heat_representation (r : PlanarPosition) :
    planarResolventMode r = ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * planarHeatAverage t r := by
  unfold planarResolventMode planarResolventKernel
  simp_rw [← integral_mul_const]
  rw [← integral_integral_swap (planarResolvent_forcing_integrable r)]
  simp_rw [planarResolventIntegrand, mul_assoc, integral_const_mul]
  rfl

theorem planarResolventMode_heat_integrable (r : PlanarPosition) :
    IntegrableOn (fun t => Real.exp (-t) * planarHeatAverage t r) (Set.Ioi (0 : ℝ)) := by
  have h := (planarResolvent_forcing_integrable r).integral_prod_left
  change Integrable _ _
  simpa only [planarResolventIntegrand, mul_assoc, integral_const_mul, planarHeatAverage] using h

theorem planarResolventMode_positive (r : PlanarPosition) : 0 < planarResolventMode r := by
  rw [planarResolventMode_heat_representation]
  have hpos (t : ℝ) (ht : t ∈ Set.Ioi (0 : ℝ)) :
      0 < Real.exp (-t) * planarHeatAverage t r :=
    mul_pos (Real.exp_pos _) (planarHeatAverage_positive ht r)
  have hae : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      (fun t => Real.exp (-t) * planarHeatAverage t r) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using (hpos t ht).le
  apply (integral_pos_iff_support_of_nonneg_ae hae (planarResolventMode_heat_integrable r)).mpr
  have hs : Set.Ioi (0 : ℝ) ⊆ support (fun t => Real.exp (-t) * planarHeatAverage t r) :=
    fun t ht => (hpos t ht).ne'
  have hm : 0 < (volume.restrict (Set.Ioi (0 : ℝ))) (Set.Ioi (0 : ℝ)) := by simp
  exact hm.trans_le (measure_mono hs)

theorem planarResolventMode_le_one (r : PlanarPosition) : planarResolventMode r ≤ 1 := by
  rw [planarResolventMode_heat_representation, ← integral_exp_neg_Ioi_zero]
  apply integral_mono_ae (planarResolventMode_heat_integrable r)
    (by simpa only [IntegrableOn, neg_mul, one_mul] using
      exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mul_le_of_le_one_right (Real.exp_pos _).le (planarHeatAverage_le_one ht r)

end ContinuumCoulomb

end

end OAI
