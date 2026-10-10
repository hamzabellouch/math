import OAI.Geometry.IsometricImmersion.Pulses.ForcingCoefficientSign
import OAI.Geometry.IsometricImmersion.Pulses.PulseMoment
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Weighted

def pulseStrip (a delta tau : ℝ) : Set Coord :=
  closedRectangle (-a) a (-(delta/tau)) (delta/tau)
def pulsePairRectangle (a delta tau : ℝ) : Set (ℝ × ℝ) :=
  Icc (-(delta/tau)) (delta/tau) ×ˢ Icc (-a) a
def pulsePairPoint (q : ℝ × ℝ) : Coord := boxPoint q.2 q.1
def pulseTest (a tau x : ℝ) : ℝ := axisBump a x*Real.cos (tau*x)
def pulseMomentWeight (a delta tau : ℝ) (q : ℝ × ℝ) : ℝ :=
  temporalCutoff (tau*q.1/delta)*(axisBump a q.2^2*Real.cos (tau*q.2)^2)
def pulseWeightedMoment (a delta tau : ℝ) (f : Coord → ℝ) : ℝ :=
  ∫ q in pulsePairRectangle a delta tau, f (pulsePairPoint q)*pulseTest a tau q.2
    ∂volume.prod volume

theorem pulsePairRectangle_isCompact (a delta tau : ℝ) :
    IsCompact (pulsePairRectangle a delta tau) := isCompact_Icc.prod isCompact_Icc

theorem pulsePairPoint_continuous : Continuous pulsePairPoint := by
  unfold pulsePairPoint boxPoint
  fun_prop

theorem pulsePairPoint_mem {a delta tau : ℝ} {q : ℝ × ℝ}
    (hq : q ∈ pulsePairRectangle a delta tau) : pulsePairPoint q ∈ pulseStrip a delta tau :=
  boxPoint_mem hq.2 hq.1

theorem pulseStrip_zero_mem {a delta tau : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ delta) (ht : 0 < tau) :
    boxPoint 0 0 ∈ pulseStrip a delta tau := by
  apply boxPoint_mem <;> constructor <;> linarith [div_nonneg hd ht.le]

theorem pulsePair_integrableOn {a delta tau : ℝ} {f : Coord → ℝ}
    (hf : ContinuousOn f (pulseStrip a delta tau)) :
    IntegrableOn (fun q => f (pulsePairPoint q)) (pulsePairRectangle a delta tau)
      (volume.prod volume) :=
  (hf.comp pulsePairPoint_continuous.continuousOn (fun _ hq => pulsePairPoint_mem hq)).integrableOn_compact
    (pulsePairRectangle_isCompact a delta tau)

theorem pulsePair_integral_eq_rectangleIntegral {a delta tau : ℝ} {f : Coord → ℝ}
    (ha : 0 ≤ a) (hd : 0 ≤ delta) (ht : 0 < tau)
    (hf : ContinuousOn f (pulseStrip a delta tau)) :
    (∫ q in pulsePairRectangle a delta tau, f (pulsePairPoint q) ∂volume.prod volume) =
      rectangleIntegral (-a) a (-(delta/tau)) (delta/tau) f := by
  have htime : -(delta/tau) ≤ delta/tau := by linarith [div_nonneg hd ht.le]
  have hspace : -a ≤ a := by linarith
  rw [show pulsePairRectangle a delta tau =
    Icc (-(delta/tau)) (delta/tau) ×ˢ Icc (-a) a from rfl,
    setIntegral_prod _ (pulsePair_integrableOn hf)]
  unfold rectangleIntegral
  rw [intervalIntegral.integral_of_le htime,←integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro theta htheta
  dsimp only
  rw [intervalIntegral.integral_of_le hspace,←integral_Icc_eq_integral_Ioc]
  rfl

theorem pulseMomentWeight_continuous (a delta tau : ℝ) :
    Continuous (pulseMomentWeight a delta tau) := by
  unfold pulseMomentWeight temporalCutoff
  exact (((axisBump_contDiff (1/2)).continuous.comp (by fun_prop)).mul
    ((((axisBump_contDiff a).continuous.comp continuous_snd).pow 2).mul (by fun_prop)))

theorem pulseMomentWeight_nonneg (a delta tau : ℝ) (q : ℝ × ℝ) :
    0 ≤ pulseMomentWeight a delta tau q :=
  mul_nonneg (axisBump_nonneg _ _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))

theorem pulseTest_continuous (a tau : ℝ) : Continuous (pulseTest a tau) :=
  (axisBump_contDiff a).continuous.mul (by fun_prop)

theorem pulseTest_hasCompactSupport {a : ℝ} (ha : 0 < a) (tau : ℝ) :
    HasCompactSupport (pulseTest a tau) := (axisBump_hasCompactSupport ha).mul_right

theorem spatial_moment_Icc_eq {a : ℝ} (ha : 0 < a) (tau : ℝ) :
    (∫ x in Icc (-a) a, axisBump a x^2*Real.cos (tau*x)^2) =
      ∫ x : ℝ, axisBump a x^2*Real.cos (tau*x)^2 := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hz : axisBump a x = 0 := by
    by_contra hn
    have h := abs_lt.mp (axisBump_support_bound ha hn)
    exact hx ⟨h.1.le,h.2.le⟩
  simp only [hz,zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_mul]

theorem temporal_pulse_integral {delta tau : ℝ} (hd : 0 < delta) (ht : 0 < tau) :
    (∫ theta in Icc (-(delta/tau)) (delta/tau), temporalCutoff (tau*theta/delta)) =
      (delta/tau)*(∫ theta : ℝ, temporalCutoff theta) := by
  have hglobal : (∫ theta : ℝ, temporalCutoff (tau*theta/delta)) =
      (delta/tau)*(∫ theta : ℝ, temporalCutoff theta) := by
    have heq : (fun theta : ℝ => temporalCutoff (tau*theta/delta)) =
        fun theta => temporalCutoff ((tau/delta)*theta) := by
      funext theta
      congr 1
      ring
    rw [heq,Measure.integral_comp_mul_left]
    simp only [inv_div,abs_of_pos (div_pos hd ht),smul_eq_mul]
  rw [←hglobal]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro theta htheta
  by_contra hn
  have h := axisBump_support_bound (by norm_num : (0 : ℝ) < 1/2) hn
  rw [abs_div,abs_mul,abs_of_pos ht,abs_of_pos hd] at h
  have hmul : tau*|theta| < delta/2 := by
    have hh := (div_lt_iff₀ hd).mp h
    linarith
  have htheta' : |theta| ≤ delta/tau := (le_div_iff₀ ht).mpr (by nlinarith)
  exact htheta (abs_le.mp htheta')

theorem pulseMomentWeight_integral {a delta tau : ℝ}
    (ha : 0 < a) (hd : 0 < delta) (ht : 0 < tau) :
    (∫ q in pulsePairRectangle a delta tau, pulseMomentWeight a delta tau q
      ∂volume.prod volume) =
      (delta/tau)*(∫ theta : ℝ, temporalCutoff theta)*
        (∫ x : ℝ, axisBump a x^2*Real.cos (tau*x)^2) := by
  rw [show pulsePairRectangle a delta tau =
    Icc (-(delta/tau)) (delta/tau) ×ˢ Icc (-a) a from rfl]
  unfold pulseMomentWeight
  rw [setIntegral_prod_mul (fun theta : ℝ => temporalCutoff (tau*theta/delta))
    (fun x : ℝ => axisBump a x^2*Real.cos (tau*x)^2)
    (Icc (-(delta/tau)) (delta/tau)) (Icc (-a) a),
    temporal_pulse_integral hd ht,spatial_moment_Icc_eq ha tau]

end SmoothLocal.Pulse

end

end OAI
