import OAI.Geometry.IsometricImmersion.Pulses.CutoffEdgeMoment
import OAI.Geometry.IsometricImmersion.Pulses.PulseTemporalParts
import OAI.Geometry.IsometricImmersion.Taylor.TaylorCauchyData

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.Taylor

theorem pulse_test_interval_eq_global {a : ℝ} (ha : 0 < a) (tau : ℝ) (f : ℝ → ℝ) :
    (∫ x in (-a)..a, pulseTest a tau x*f x) =
      ∫ x : ℝ, axisBump a x*f x*Real.cos (tau*x) := by
  rw [intervalIntegral.integral_of_le (by linarith : -a ≤ a),←integral_Icc_eq_integral_Ioc]
  calc
    _ = ∫ x in Icc (-a) a, axisBump a x*f x*Real.cos (tau*x) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro _ _
      unfold pulseTest
      ring
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hz : axisBump a x = 0 := by
        by_contra hn
        have hs := abs_lt.mp (axisBump_support_bound ha hn)
        exact hx ⟨hs.1.le,hs.2.le⟩
      simp only [hz,zero_mul]

theorem pulse_test_interval_finite_bound {a B tau : ℝ} {f : ℝ → ℝ} {I : Set ℝ}
    (ha : 0 < a) (hB : 0 ≤ B) (htau : 0 < tau)
    (hI : IsOpen I) (hf : ContDiffOn ℝ ∞ f I) (hsub : Icc (-a) a ⊆ I) (N : ℕ)
    (hjet : ∀ k ≤ N, ∀ x ∈ Icc (-a) a, ‖iteratedFDeriv ℝ k f x‖ ≤ B) :
    |∫ x in (-a)..a, pulseTest a tau x*f x| ≤
      ((2*a)*cutoffEdgeDerivativeBound a ha N B)/tau^N := by
  rw [pulse_test_interval_eq_global ha]
  exact cutoffEdgeWeight_cos_integral_bound ha hB htau hI hf hsub N hjet

theorem pulse_boxPoint_eq (x t : ℝ) : boxPoint x t = (![x,t] : Coord) := by
  ext i
  fin_cases i
  · change boxPoint x t 0=x
    exact pulse_boxPoint_zero x t
  · change boxPoint x t 1=t
    exact pulse_boxPoint_one x t

theorem pulse_temporal_moment_finite_bound {a B delta tau : ℝ}
    {v : Coord → ℝ} {U : Set Coord} {I : Set ℝ}
    (ha : 0 < a) (hB : 0 ≤ B) (hd : 0 ≤ delta) (htau : 0 < tau)
    (hv : ContDiffOn ℝ ∞ v U) (hU : IsOpen U) (hSU : pulseStrip a delta tau ⊆ U)
    (hI : IsOpen I) (hsub : Icc (-a) a ⊆ I)
    (hupper : ∀ x ∈ I, (![x,delta/tau] : Coord) ∈ U)
    (hinitial : ∀ x ∈ Icc (-a) a, coordPartial 1 v (boxPoint x (-(delta/tau))) = 0)
    (N : ℕ)
    (hjet : ∀ k ≤ N, ∀ x ∈ Icc (-a) a,
      ‖iteratedFDeriv ℝ k (heightCauchyVelocity v (delta/tau)) x‖ ≤ B) :
    |rectangleIntegral (-a) a (-(delta/tau)) (delta/tau)
      (fun p => pulseSpatialTest a tau p*coordPartial 1 (coordPartial 1 v) p)| ≤
      ((2*a)*cutoffEdgeDerivativeBound a ha N B)/tau^N := by
  rw [pulse_temporal_second_parts_zero_initial ha hd htau hv hU hSU hinitial]
  have hf := heightCauchyVelocity_contDiffOn hv hU (delta/tau) hupper
  have hb := pulse_test_interval_finite_bound ha hB htau hI hf hsub N hjet
  simpa only [heightCauchyVelocity,pulse_boxPoint_eq] using hb

theorem finite_edge_absorption_threshold {a B c3 : ℝ} (ha : 0 < a) (_hB : 0 ≤ B)
    (hc3 : 0 < c3) (N : ℕ) (delta : ℝ) (hdelta : 0 < delta) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ tau : ℝ, T ≤ tau →
      ((2*a)*cutoffEdgeDerivativeBound a ha N B)/tau^N ≤
        (c3/2)*delta*tau/tau^N := by
  let C := (2*a)*cutoffEdgeDerivativeBound a ha N B
  refine ⟨max 1 (2*C/(c3*delta)),le_max_left _ _,?_⟩
  intro tau htau
  have ht1 : 1 ≤ tau := (le_max_left _ _).trans htau
  have htpos : 0 < tau := zero_lt_one.trans_le ht1
  have hthreshold : 2*C/(c3*delta) ≤ tau := (le_max_right _ _).trans htau
  have hh := (div_le_iff₀ (mul_pos hc3 hdelta)).mp hthreshold
  have hnum : C ≤ (c3/2)*delta*tau := by nlinarith
  exact div_le_div_of_nonneg_right hnum (pow_nonneg htpos.le N)

end SmoothLocal.Pulse

end

end OAI
