import Mathlib
import OAI.Analysis.CoulombIonization.Variational.TruncatedCoulomb
import OAI.Analysis.CoulombIonization.RadialBounds.CoulombBallIntegral

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

def truncatedInvSquare (R : ℝ) : TFSpace → ℝ :=
  (ball 0 R).indicator (fun x => ‖x‖⁻¹^2)

lemma truncatedInvSquare_nonneg (R : ℝ) (x : TFSpace) : 0 ≤ truncatedInvSquare R x :=
  indicator_nonneg (fun _ _ => sq_nonneg _) _

lemma truncatedInvSquare_integrable (R : ℝ) : Integrable (truncatedInvSquare R) := by
  have hi : IntegrableOn (fun x : TFSpace => ‖x‖^(-2:ℝ)) (ball 0 R) := by
    apply integrableOn_ball_of_norm_le_rpow (by simp [TFSpace])
      (by norm_num [TFSpace] : (2:ℝ) < Module.finrank ℝ TFSpace) (C := 1)
    · exact Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),one_mul]
    · exact (measurable_norm.pow_const _).aestronglyMeasurable
  have hh := hi.integrable_indicator measurableSet_ball
  convert hh using 1
  funext x
  norm_num [truncatedInvSquare,Real.rpow_neg,Real.rpow_two,inv_pow]

lemma truncatedInvSquare_integral {R : ℝ} (hR : 0 < R) :
    (∫ x, truncatedInvSquare R x) = 4*Real.pi*R := by
  rw [truncatedInvSquare,integral_indicator measurableSet_ball]
  have hh := integral_norm_rpow_ball hR (by norm_num : (-3:ℝ) < -2)
  norm_num [Real.rpow_neg,Real.rpow_two,inv_pow] at hh
  simpa only [inv_pow] using hh

lemma bounded_support_memLp {ρ : TFSpace → ℝ} (hm : Measurable ρ) {M S : ℝ}
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M)
    (hs : Function.support ρ ⊆ ball 0 S) (p : ENNReal) : MemLp ρ p := by
  have hc : HasCompactSupport ρ := HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : TFSpace) S) (hs.trans ball_subset_closedBall)
  exact hc.memLp_of_bound hm.aestronglyMeasurable M
    (Eventually.of_forall fun z => by simpa only [Real.norm_of_nonneg (hn z)] using hb z)

lemma bounded_support_integrable {ρ : TFSpace → ℝ} (hm : Measurable ρ) {M S : ℝ}
    (hn : ∀ z, 0 ≤ ρ z) (hb : ∀ z, ρ z ≤ M)
    (hs : Function.support ρ ⊆ ball 0 S) : Integrable ρ :=
  memLp_one_iff_integrable.mp (bounded_support_memLp hm hn hb hs 1)

lemma coulomb_inv_difference {x y z : TFSpace} (hx : z ≠ x) (hy : z ≠ y) :
    |‖x-z‖⁻¹-‖y-z‖⁻¹| ≤ ‖x-y‖*(‖x-z‖⁻¹^2+‖y-z‖⁻¹^2)/2 := by
  have ha : 0 < ‖x-z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx.symm)
  have hb : 0 < ‖y-z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hy.symm)
  have he : ‖x-z‖⁻¹-‖y-z‖⁻¹ = (‖y-z‖-‖x-z‖)/(‖x-z‖*‖y-z‖) := by field_simp
  have hd : |‖y-z‖-‖x-z‖| ≤ ‖x-y‖ := by
    have hh := abs_norm_sub_norm_le (y-z) (x-z)
    simpa only [sub_sub_sub_cancel_right,norm_sub_rev] using hh
  rw [he,abs_div,abs_of_nonneg (mul_nonneg ha.le hb.le)]
  calc
    _ ≤ ‖x-y‖/(‖x-z‖*‖y-z‖) := div_le_div_of_nonneg_right hd (mul_nonneg ha.le hb.le)
    _ = ‖x-y‖*(‖x-z‖⁻¹*‖y-z‖⁻¹) := by ring
    _ ≤ ‖x-y‖*((‖x-z‖⁻¹^2+‖y-z‖⁻¹^2)/2) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      nlinarith [sq_nonneg (‖x-z‖⁻¹-‖y-z‖⁻¹)]
    _ = _ := by ring

lemma support_distance_lt {ρ : TFSpace → ℝ} {S : ℝ}
    (hs : Function.support ρ ⊆ ball 0 S) {x z : TFSpace} (hx : ‖x‖ ≤ S) (hz : ρ z ≠ 0) :
    ‖x-z‖ < 2*S := by
  have hh : ‖z‖ < S := mem_ball_zero_iff.mp (hs hz)
  exact (norm_sub_le x z).trans_lt (by linarith)

theorem bounded_density_potential_le {ρ : TFSpace → ℝ} (hm : Measurable ρ)
    {M S : ℝ} (hM : 0 ≤ M) (hS : 0 < S) (hn : ∀ z, 0 ≤ ρ z)
    (hb : ∀ z, ρ z ≤ M) (hs : Function.support ρ ⊆ ball 0 S)
    (x : TFSpace) (hx : ‖x‖ ≤ S) : tfPotential ρ x ≤ 8*Real.pi*M*S^2 := by
  have hk := (tfSubMap_preserving x).integrable_comp (truncatedCoulomb_integrable (2*S)).aestronglyMeasurable
    |>.mpr (truncatedCoulomb_integrable (2*S))
  have hi := tfPotential_integrable (bounded_support_integrable hm hn hb hs)
    (bounded_support_memLp hm hn hb hs (5/3)) x
  have hh : (∫ z, ρ z/‖x-z‖) ≤ ∫ z, M*truncatedCoulomb (2*S) (x-z) := by
    apply integral_mono hi (hk.const_mul M)
    intro z
    change ρ z/‖x-z‖ ≤ M*truncatedCoulomb (2*S) (x-z)
    by_cases hz : ρ z = 0
    · simp only [hz,zero_div]
      exact mul_nonneg hM (truncatedCoulomb_nonneg _ _)
    · rw [truncatedCoulomb,indicator_of_mem (mem_ball_zero_iff.mpr (support_distance_lt hs hx hz))]
      exact (div_le_div_of_nonneg_right (hb z) (norm_nonneg _)).trans_eq (by ring)
  change (∫ z, ρ z/‖x-z‖) ≤ _
  apply hh.trans_eq
  rw [integral_const_mul,integral_sub_left_eq_self,truncatedCoulomb,integral_indicator measurableSet_ball]
  simp only [one_div]
  rw [integral_coulomb_ball (by linarith : 0 < 2*S)]
  ring

theorem bounded_density_potential_difference {ρ : TFSpace → ℝ} (hm : Measurable ρ)
    {M S : ℝ} (hM : 0 ≤ M) (hS : 0 < S) (hn : ∀ z, 0 ≤ ρ z)
    (hb : ∀ z, ρ z ≤ M) (hs : Function.support ρ ⊆ ball 0 S)
    (x y : TFSpace) (hx : ‖x‖ ≤ S) (hy : ‖y‖ ≤ S) :
    |tfPotential ρ x-tfPotential ρ y| ≤ 8*Real.pi*M*S*‖x-y‖ := by
  have hi (w : TFSpace) := tfPotential_integrable (bounded_support_integrable hm hn hb hs)
    (bounded_support_memLp hm hn hb hs (5/3)) w
  have hk (w : TFSpace) : Integrable (fun z => truncatedInvSquare (2*S) (w-z)) :=
    (tfSubMap_preserving w).integrable_comp (truncatedInvSquare_integrable (2*S)).aestronglyMeasurable
      |>.mpr (truncatedInvSquare_integrable (2*S))
  have he : (∫ z, ρ z/‖x-z‖-ρ z/‖y-z‖) = tfPotential ρ x-tfPotential ρ y :=
    integral_sub (hi x) (hi y)
  rw [←he]
  apply abs_integral_le_integral_abs.trans
  calc
    _ ≤ ∫ z, (M*‖x-y‖/2)*(truncatedInvSquare (2*S) (x-z)+truncatedInvSquare (2*S) (y-z)) := by
      apply integral_mono_ae ((hi x).sub (hi y)).abs (((hk x).add (hk y)).const_mul _)
      filter_upwards [volume.ae_ne x,volume.ae_ne y] with z hzx hzy
      change |ρ z/‖x-z‖-ρ z/‖y-z‖| ≤
        (M*‖x-y‖/2)*(truncatedInvSquare (2*S) (x-z)+truncatedInvSquare (2*S) (y-z))
      by_cases hz : ρ z = 0
      · simp only [hz,zero_div,sub_self,abs_zero]
        exact mul_nonneg (by positivity) (add_nonneg (truncatedInvSquare_nonneg _ _) (truncatedInvSquare_nonneg _ _))
      · rw [truncatedInvSquare,indicator_of_mem (mem_ball_zero_iff.mpr (support_distance_lt hs hx hz)),
          indicator_of_mem (mem_ball_zero_iff.mpr (support_distance_lt hs hy hz))]
        rw [div_eq_mul_inv,div_eq_mul_inv,←mul_sub,abs_mul,abs_of_nonneg (hn z)]
        calc
          _ ≤ ρ z*(‖x-y‖*(‖x-z‖⁻¹^2+‖y-z‖⁻¹^2)/2) :=
            mul_le_mul_of_nonneg_left (coulomb_inv_difference hzx hzy) (hn z)
          _ ≤ M*(‖x-y‖*(‖x-z‖⁻¹^2+‖y-z‖⁻¹^2)/2) :=
            mul_le_mul_of_nonneg_right (hb z) (by positivity)
          _ = _ := by ring
    _ = _ := by
      rw [integral_const_mul,integral_add (hk x) (hk y),integral_sub_left_eq_self,integral_sub_left_eq_self,
        truncatedInvSquare_integral (by linarith : 0 < 2*S)]
      ring

end CoulombAnalysis

end

end OAI
