import Mathlib
import OAI.Analysis.Conductivity.Variational.CrossingProfiles
import OAI.Analysis.Conductivity.Fourier.ModeConnector

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

lemma connectorProfile_left {K z : ℝ} (hK : 0 < K) (hz : z ≤ 1) :
    connectorProfile K z = exp (-z/2) := by
  have hi : (∫ t in (0:ℝ)..z, connectorRate K t) = z/2 := by
    calc
      _ = ∫ _t in (0:ℝ)..z, (1/2:ℝ) := intervalIntegral.integral_congr (by
        intro t ht
        exact connectorRate_left hK ((le_max_iff.mp ht.2).elim (by intro h; linarith) (by intro h; linarith)))
      _ = _ := by simp; ring
  rw [connectorProfile,hi]
  congr 1
  ring

lemma connectorProfile_right {K z : ℝ} (hK : 0 < K) (hz : K+1 ≤ z) :
    connectorProfile K z = connectorProfile K (K+2)*exp (-3*(z-(K+2))) := by
  have hi : (∫ t in (K+2)..z, connectorRate K t) = 3*(z-(K+2)) := by
    calc
      _ = ∫ _t in (K+2)..z, (3:ℝ) := intervalIntegral.integral_congr (by
        intro t ht
        apply connectorRate_right hK
        exact le_trans (le_min (by linarith) hz) ht.1)
      _ = _ := by simp; ring
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((connectorRate_smooth K).continuous.intervalIntegrable 0 (K+2))
    ((connectorRate_smooth K).continuous.intervalIntegrable (K+2) z)
  rw [hi] at hadd
  unfold connectorProfile
  rw [←hadd,neg_add,exp_add]
  congr 2
  ring

def cascadeProfile (L K t : ℝ) : ℝ :=
  crossingOn L (t/2+L) * connectorProfile K t * crossingOff L (t-(K+2+L))

lemma cascadeProfile_smooth (L K : ℝ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (cascadeProfile L K) := by
  exact (((crossingOn_smooth L).comp ((contDiff_id.div_const 2).add contDiff_const)).mul
    (connectorProfile_smooth K)).mul ((crossingOff_smooth L).comp (contDiff_id.sub contDiff_const))

lemma cascadeProfile_nonneg (L K t : ℝ) : 0 ≤ cascadeProfile L K t :=
  mul_nonneg (mul_nonneg (crossingOn_bounds L _).1 (connectorProfile_pos K t).le)
    (crossingOff_bounds L _).1

lemma cascadeProfile_zero_left {L K t : ℝ} (hL : 0 < L) (ht : t ≤ -7*L/2) :
    cascadeProfile L K t = 0 := by
  rw [cascadeProfile,crossingOn_eq_zero hL (show t/2+L ≤ -3*L/4 by linarith),zero_mul,zero_mul]
lemma cascadeProfile_zero_right {L K t : ℝ} (hL : 0 < L) (ht : K+2+7*L/4 ≤ t) :
    cascadeProfile L K t = 0 := by
  rw [cascadeProfile,crossingOff_eq_zero hL (show 3*L/4 ≤ t-(K+2+L) by linarith),mul_zero]

lemma cascadeProfile_compact {L K : ℝ} (hL : 0 < L) : HasCompactSupport (cascadeProfile L K) := by
  apply HasCompactSupport.intro (K := Icc (-7*L/2) (K+2+7*L/4)) isCompact_Icc
  intro t ht
  rw [mem_Icc,not_and_or,not_le,not_le] at ht
  rcases ht with ht | ht
  · exact cascadeProfile_zero_left hL ht.le
  · exact cascadeProfile_zero_right hL ht.le

lemma cascadeProfile_connector {L K t : ℝ} (hL : 0 < L) (ht₁ : 0 ≤ t) (ht₂ : t ≤ K+2) :
    cascadeProfile L K t = connectorProfile K t := by
  rw [cascadeProfile,crossingOn_eq_one hL (show -L/2 ≤ t/2+L by linarith),
    crossingOff_eq_one hL (show t-(K+2+L) ≤ L/2 by linarith)]
  ring

lemma cascadeProfile_incoming {L K t : ℝ} (hL : 0 < L) (hK : 0 < K) (ht : t ≤ 0) :
    cascadeProfile L K t = crossingOn L (t/2+L)*exp (-t/2) := by
  rw [cascadeProfile,connectorProfile_left hK (show t≤1 by linarith),
    crossingOff_eq_one hL (show t-(K+2+L) ≤ L/2 by linarith),mul_one]

lemma cascadeProfile_outgoing {L K t : ℝ} (hL : 0 < L) (hK : 0 < K) (ht : K+2 ≤ t) :
    cascadeProfile L K t = connectorProfile K (K+2)*exp (-3*(t-(K+2))) *
      crossingOff L (t-(K+2+L)) := by
  rw [cascadeProfile,crossingOn_eq_one hL (show -L/2≤t/2+L by linarith),one_mul,
    connectorProfile_right hK (show K+1≤t by linarith)]

def cascadeRatio (L K : ℝ) : ℝ := exp (-4*L)*connectorProfile K (K+2)

def cascadeLength (L K : ℝ) : ℝ := K+2+2*L

lemma cascadeRatio_pos (L K : ℝ) : 0 < cascadeRatio L K :=
  mul_pos (exp_pos _) (connectorProfile_pos _ _)

lemma cascadeRatio_small {L K : ℝ} (hL : 1 ≤ L) (hK : 0 < K) :
    4*cascadeRatio L K < 1 := by
  have he : exp (-4*L) < 1/4 := by
    rw [neg_mul,exp_neg,one_div,inv_lt_inv₀ (exp_pos _) (by norm_num : (0:ℝ)<4)]
    have := add_one_le_exp (4*L)
    linarith
  have hc := connectorProfile_le_one (K := K) (z := K+2) (by linarith)
  have hq : cascadeRatio L K ≤ exp (-4*L) := by
    exact (mul_le_mul_of_nonneg_left hc (exp_pos _).le).trans_eq (mul_one _)
  linarith

lemma cascade_length_positive {L K : ℝ} (hL : 0 < L) (hK : 0 < K) :
    0 < cascadeLength L K := by unfold cascadeLength; linarith

end ScalarConductivity

end

end OAI
