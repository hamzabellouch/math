import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarResolvent

namespace OAI

/-! Positivity, finite L² normalization and compact support of the actual
manufactured planar potential. The differential eigen-equation and gap are
not assumed by these declarations. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarResolventKernel_integral : (∫ r, planarResolventKernel r) = 1 := by
  unfold planarResolventKernel
  rw [← integral_integral_swap (f := fun t r => planarResolventIntegrand (t, r))
    planarResolventIntegrand_integrable]
  calc
    _ = ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simp only [planarResolventIntegrand, integral_const_mul, planarHeatKernel_integral ht, mul_one]
    _ = 1 := integral_exp_neg_Ioi_zero

theorem planarResolventMode_integrable : Integrable planarResolventMode :=
  planarResolventKernel_integrable.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ)
    planarForcing_integrable

theorem planarResolventMode_integral : (∫ r, planarResolventMode r) = ∫ r, planarForcing r := by
  have h := integral_convolution (ContinuousLinearMap.mul ℝ ℝ)
    planarResolventKernel_integrable planarForcing_integrable
  simpa only [planarResolventKernel_integral, ContinuousLinearMap.mul_apply', one_mul,
    planarResolventMode, convolution] using h

theorem planarResolventMode_square_integrable : Integrable (fun r => planarResolventMode r ^ 2) := by
  apply planarResolventMode_integrable.mono'
    (planarResolventMode_C7.continuous.pow 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun r => by
    change ‖planarResolventMode r ^ 2‖ ≤ planarResolventMode r
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hp := planarResolventMode_positive r
    have hb := planarResolventMode_le_one r
    nlinarith)

theorem planarResolventMode_memLp : MemLp planarResolventMode 2 :=
  (memLp_two_iff_integrable_sq planarResolventMode_C7.continuous.aestronglyMeasurable).mpr
    planarResolventMode_square_integrable

theorem planarResolventMode_square_integral_positive :
    0 < ∫ r, planarResolventMode r ^ 2 :=
  integral_pos_of_integrable_nonneg_nonzero (planarResolventMode_C7.continuous.pow 2)
    planarResolventMode_square_integrable (fun _ => sq_nonneg _)
    (sq_pos_of_pos (planarResolventMode_positive 0)).ne'

def normalizedPlanarMode (r : PlanarPosition) : ℝ :=
  planarResolventMode r / Real.sqrt (∫ s, planarResolventMode s ^ 2)

theorem normalizedPlanarMode_C7 : ContDiff ℝ 7 normalizedPlanarMode :=
  planarResolventMode_C7.div_const _

theorem normalizedPlanarMode_positive (r : PlanarPosition) : 0 < normalizedPlanarMode r :=
  div_pos (planarResolventMode_positive r) (Real.sqrt_pos.mpr planarResolventMode_square_integral_positive)

theorem normalizedPlanarMode_normalized : (∫ r, normalizedPlanarMode r ^ 2) = 1 := by
  simp_rw [normalizedPlanarMode, div_pow]
  rw [integral_div, Real.sq_sqrt planarResolventMode_square_integral_positive.le,
    div_self planarResolventMode_square_integral_positive.ne']

def manufacturedPlanarWell (r : PlanarPosition) : ℝ :=
  -planarForcing r / (2 * planarResolventMode r)

theorem manufacturedPlanarWell_C7 : ContDiff ℝ 7 manufacturedPlanarWell :=
  planarForcing_C7.neg.div (contDiff_const.mul planarResolventMode_C7)
    (fun r => mul_ne_zero (by norm_num) (planarResolventMode_positive r).ne')

theorem manufacturedPlanarWell_nonpositive (r : PlanarPosition) : manufacturedPlanarWell r ≤ 0 :=
  div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (planarForcing_nonnegative r))
    (mul_nonneg (by norm_num) (planarResolventMode_positive r).le)

theorem manufacturedPlanarWell_support : tsupport manufacturedPlanarWell ⊆ tsupport planarForcing := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro r hr
  by_contra hn
  apply hr
  change -planarForcing r / (2 * planarResolventMode r) = 0
  rw [image_eq_zero_of_notMem_tsupport hn, neg_zero, zero_div]

theorem manufacturedPlanarWell_hasCompactSupport : HasCompactSupport manufacturedPlanarWell :=
  planarForcing_hasCompactSupport.of_isClosed_subset (isClosed_tsupport _)
    manufacturedPlanarWell_support

end ContinuumCoulomb

end

end OAI
