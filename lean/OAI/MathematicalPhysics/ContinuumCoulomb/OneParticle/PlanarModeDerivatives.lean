import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarModeProperties

namespace OAI

/-! Actual first and second directional derivatives of the resolvent mode.
Differentiation is transferred to the compact forcing, which also gives
finite L¹ and L² derivatives without differentiating the singular kernel. -/

noncomputable section
open MeasureTheory
open scoped Convolution
namespace ContinuumCoulomb

theorem planarResolventKernel_nonnegative (r : PlanarPosition) :
    0 ≤ planarResolventKernel r := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mul_nonneg (Real.exp_pos _).le (planarHeatKernel_positive ht r).le

def planarResolventOf (g : PlanarPosition → ℝ) (r : PlanarPosition) : ℝ :=
  ∫ b, planarResolventKernel b * g (r - b)

theorem planarResolventOf_integrable {g : PlanarPosition → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) : Integrable (planarResolventOf g) :=
  planarResolventKernel_integrable.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ)
    (hg.integrable_of_hasCompactSupport hc)

theorem planarResolventOf_continuous {g : PlanarPosition → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) : Continuous (planarResolventOf g) :=
  hc.continuous_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    planarResolventKernel_integrable.locallyIntegrable hg

theorem planarResolventOf_bound {g : PlanarPosition → ℝ} {B : ℝ}
    (hB : ∀ x, ‖g x‖ ≤ B) (r : PlanarPosition) : ‖planarResolventOf g r‖ ≤ B := by
  have h := norm_integral_le_of_norm_le (planarResolventKernel_integrable.mul_const B)
    (Filter.Eventually.of_forall (fun b => show
      ‖planarResolventKernel b * g (r - b)‖ ≤ planarResolventKernel b * B by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (planarResolventKernel_nonnegative b)]
      exact mul_le_mul_of_nonneg_left (hB _) (planarResolventKernel_nonnegative b)))
  simpa only [integral_mul_const, planarResolventKernel_integral, one_mul,
    planarResolventOf] using h

theorem planarResolventOf_square_integrable {g : PlanarPosition → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) :
    Integrable (fun r => planarResolventOf g r ^ 2) := by
  obtain ⟨B, hB⟩ := hg.bounded_above_of_compact_support hc
  have hi := (planarResolventOf_integrable hg hc).norm.const_mul B
  apply hi.mono' ((planarResolventOf_continuous hg hc).pow 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun r => by
    change ‖planarResolventOf g r ^ 2‖ ≤ B * ‖planarResolventOf g r‖
    have hb := planarResolventOf_bound hB r
    rw [norm_pow]
    exact (pow_two (‖planarResolventOf g r‖)).trans_le
      (mul_le_mul_of_nonneg_right hb (norm_nonneg _)))

theorem planarResolventOf_partial {g : PlanarPosition → ℝ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (e r : PlanarPosition) :
    planarPartial (planarResolventOf g) e r = planarResolventOf (planarPartial g e) r := by
  have hd := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    planarResolventKernel_integrable.locallyIntegrable hg r
  have hi := (hc.fderiv ℝ).convolutionExists_right
    ((ContinuousLinearMap.mul ℝ ℝ).precompR PlanarPosition)
    planarResolventKernel_integrable.locallyIntegrable
    (hg.continuous_fderiv (by norm_num)) r
  change fderiv ℝ (planarResolventOf g) r e = _
  rw [show fderiv ℝ (planarResolventOf g) r =
    (planarResolventKernel ⋆[((ContinuousLinearMap.mul ℝ ℝ).precompR PlanarPosition), volume]
      fderiv ℝ g) r from hd.fderiv]
  change (∫ b, (ContinuousLinearMap.mul ℝ ℝ).precompR PlanarPosition
    (planarResolventKernel b) (fderiv ℝ g (r - b))) e = _
  rw [ContinuousLinearMap.integral_apply hi e]
  rfl

theorem planarResolventMode_partial (e r : PlanarPosition) :
    planarPartial planarResolventMode e r = planarResolventOf (planarPartial planarForcing e) r :=
  planarResolventOf_partial (planarForcing_C7.of_le (by norm_num))
    planarForcing_hasCompactSupport e r

theorem planarResolventMode_partial_integrable (e : PlanarPosition) :
    Integrable (planarPartial planarResolventMode e) := by
  change Integrable (fun r => planarPartial planarResolventMode e r)
  simp_rw [planarResolventMode_partial]
  exact planarResolventOf_integrable
    (planarPartial_continuous (planarForcing_C7.of_le (by norm_num)) e)
    (planarForcing_hasCompactSupport.fderiv_apply ℝ e)

theorem planarResolventMode_partial_square_integrable (e : PlanarPosition) :
    Integrable (fun r => planarPartial planarResolventMode e r ^ 2) := by
  simp_rw [planarResolventMode_partial]
  exact planarResolventOf_square_integrable
    (planarPartial_continuous (planarForcing_C7.of_le (by norm_num)) e)
    (planarForcing_hasCompactSupport.fderiv_apply ℝ e)

theorem planarResolventMode_partial_partial (e v r : PlanarPosition) :
    planarPartial (planarPartial planarResolventMode e) v r =
      planarResolventOf (planarPartial (planarPartial planarForcing e) v) r := by
  rw [show planarPartial planarResolventMode e =
    planarResolventOf (planarPartial planarForcing e) from funext (planarResolventMode_partial e)]
  exact planarResolventOf_partial
    (planarPartial_C1 (planarForcing_C7.of_le (by norm_num)) e)
    (planarForcing_hasCompactSupport.fderiv_apply ℝ e) v r

theorem planarResolventMode_partial_partial_square_integrable (e v : PlanarPosition) :
    Integrable (fun r => planarPartial (planarPartial planarResolventMode e) v r ^ 2) := by
  simp_rw [planarResolventMode_partial_partial]
  exact planarResolventOf_square_integrable
    (planarPartial_continuous (planarPartial_C1 (planarForcing_C7.of_le (by norm_num)) e) v)
    ((planarForcing_hasCompactSupport.fderiv_apply ℝ e).fderiv_apply ℝ v)

theorem planarResolventMode_partial_partial_integrable (e v : PlanarPosition) :
    Integrable (planarPartial (planarPartial planarResolventMode e) v) := by
  change Integrable (fun r => planarPartial (planarPartial planarResolventMode e) v r)
  simp_rw [planarResolventMode_partial_partial]
  exact planarResolventOf_integrable
    (planarPartial_continuous (planarPartial_C1 (planarForcing_C7.of_le (by norm_num)) e) v)
    ((planarForcing_hasCompactSupport.fderiv_apply ℝ e).fderiv_apply ℝ v)

end ContinuumCoulomb

end

end OAI
