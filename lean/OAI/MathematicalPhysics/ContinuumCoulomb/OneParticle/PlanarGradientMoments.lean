import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedHigherMoments
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedModeDerivatives
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarResolventTails
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.GaussianJetBounds

namespace OAI

/-! Polynomially weighted square integrability of the actual orbital's
planar derivatives, using the published construction's compact forcing. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

private theorem planarResolventOf_half_envelope {g : PlanarPosition → ℝ} {B : ℝ}
    (hg : Continuous g) (hs : tsupport g ⊆ Metric.closedBall 0 1)
    (hB : ∀ x, ‖g x‖ ≤ B) (r : PlanarPosition) :
    ‖planarResolventOf g r‖ ≤ B*planarExponentialConstant (1/2)*Real.exp (-‖r‖/2) := by
  have hB0 : 0 ≤ B := (norm_nonneg (g 0)).trans (hB 0)
  by_cases hr : r = 0
  · subst r
    simp only [norm_zero,neg_zero,zero_div,Real.exp_zero,mul_one]
    apply (planarResolventOf_bound hB 0).trans
    apply le_mul_of_one_le_right hB0
    unfold planarExponentialConstant
    have he := Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1/2)
    apply (le_div_iff₀ (by norm_num : (0:ℝ) < 1-(1/2)^2)).mpr
    nlinarith only [he]
  have hr0 : 0 < ‖r‖ := norm_pos_iff.mpr hr
  let e : PlanarPosition := ((1/2)/‖r‖) • r
  have he : ‖e‖ = 1/2 := by
    dsimp [e]
    rw [norm_smul,Real.norm_of_nonneg (by positivity)]
    field_simp
  have hi : inner ℝ e r = ‖r‖/2 := by
    dsimp [e]
    rw [real_inner_smul_left,real_inner_self_eq_norm_sq]
    field_simp
  have ht := planarResolventOf_tilt_bound hg hs hB e r (by rw [he]; norm_num)
  rw [he,hi] at ht
  convert ht using 1
  unfold planarExponentialConstant
  rw [show (1/2:ℝ)-‖r‖/2 = 1/2+(-‖r‖/2) by ring,Real.exp_add]
  ring

private theorem planarResolventOf_weighted_square_integrable {g : PlanarPosition → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ Metric.closedBall 0 1) (k : ℕ) :
    Integrable (fun r : PlanarPosition => ‖r‖^k*planarResolventOf g r^2) := by
  obtain ⟨B,hB⟩ := hg.bounded_above_of_compact_support hc
  let C := (B*planarExponentialConstant (1/2))^2*((k.factorial:ℝ)/(1/2)^k)
  have hi := (planar_exp_norm_integrable (by norm_num : (0:ℝ)<1/2)).const_mul C
  apply hi.mono' (((continuous_norm.pow k).mul
    ((planarResolventOf_continuous hg hc).pow 2)).aestronglyMeasurable)
  filter_upwards [] with r
  change ‖‖r‖^k*planarResolventOf g r^2‖ ≤ C*Real.exp (-(1/2:ℝ)*‖r‖)
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _) (sq_nonneg _))]
  have he := pow_le_pow_left₀ (norm_nonneg (planarResolventOf g r))
    (planarResolventOf_half_envelope hg hs hB r) 2
  rw [Real.norm_eq_abs,sq_abs] at he
  have hex : Real.exp (-‖r‖/2)^2 = Real.exp (-(1/2:ℝ)*‖r‖)*Real.exp (-(1/2:ℝ)*‖r‖) := by
    rw [pow_two]
    congr 1 <;> congr 1 <;> ring
  rw [mul_pow,hex] at he
  have hp := power_exponential_bound k (by norm_num : (0:ℝ)<1/2) (norm_nonneg r)
  have hm := mul_le_mul_of_nonneg_left he (pow_nonneg (norm_nonneg r) k)
  calc
    _ ≤ ‖r‖^k*((B*planarExponentialConstant (1/2))^2*
        (Real.exp (-(1/2:ℝ)*‖r‖)*Real.exp (-(1/2:ℝ)*‖r‖))) := hm
    _ = (B*planarExponentialConstant (1/2))^2*(‖r‖^k*Real.exp (-(1/2:ℝ)*‖r‖))*
        Real.exp (-(1/2:ℝ)*‖r‖) := by ring
    _ ≤ C*Real.exp (-(1/2:ℝ)*‖r‖) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (sq_nonneg _)) (Real.exp_pos _).le

theorem normalizedPlanarMode_partial_moment_integrable (e : PlanarPosition) (k : ℕ) :
    Integrable (fun r => ‖r‖^k*planarPartial normalizedPlanarMode e r^2) := by
  have hi := planarResolventOf_weighted_square_integrable
    (planarPartial_continuous (planarForcing_C7.of_le (by norm_num)) e)
    (planarForcing_hasCompactSupport.fderiv_apply ℝ e)
    ((tsupport_fderiv_apply_subset ℝ e).trans planarForcing_support) k
  simp_rw [normalizedPlanarMode_partial,planarResolventMode_partial,mul_pow]
  convert hi.const_mul ((Real.sqrt (∫ s, planarResolventMode s^2))⁻¹^2) using 1
  funext r
  ring

end ContinuumCoulomb

end

end OAI
