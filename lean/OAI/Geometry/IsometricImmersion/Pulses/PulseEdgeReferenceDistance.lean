import OAI.Geometry.IsometricImmersion.Pulses.OffPulseMetricBounds
import OAI.Geometry.IsometricImmersion.Comparison.ShearFirstJetComparison
import OAI.Geometry.IsometricImmersion.Comparison.CurvatureFullJetComparison

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem actual_sheared_reference_first_distance_of_locality
    {gStar gTau test : MetricField} {U V : Set Coord}
    (hgTau : SmoothPositiveOn gTau U) (hgStar : SmoothPositiveOn gStar V)
    (hU : IsOpen U) (hV : IsOpen V) {q0 e : ℝ} (hq0 : |q0| ≤ 1) (he : 0 ≤ e)
    {p : Coord} (hpU : inverseShearCoordinates q0 p ∈ U) (hpV : inverseShearCoordinates q0 p ∈ V)
    (hlocal : test =ᶠ[𝓝 (inverseShearCoordinates q0 p)] gStar)
    (happrox : ∀ i j : Fin 2, ∀ k ≤ 1,
      ‖iteratedFDeriv ℝ k (fun q => gTau q i j - test q i j) (inverseShearCoordinates q0 p)‖ ≤ e) :
    ‖actualCurvatureFirstInput (metricInShearCoordinates gStar q0) p -
      actualCurvatureFirstInput (metricInShearCoordinates gTau q0) p‖ ≤ 8 * e := by
  let W := U ∩ V
  have hW : IsOpen W := hU.inter hV
  have hgTW : SmoothPositiveOn gTau W :=
    ⟨fun i j => (hgTau.1 i j).mono inter_subset_left, fun q hq => hgTau.2 q hq.1⟩
  have hgSW : SmoothPositiveOn gStar W :=
    ⟨fun i j => (hgStar.1 i j).mono inter_subset_right, fun q hq => hgStar.2 q hq.2⟩
  have hpW : inverseShearCoordinates q0 p ∈ W := ⟨hpU, hpV⟩
  have hdiff : ∀ i j : Fin 2, ∀ k ≤ 1,
      ‖iteratedFDeriv ℝ k (fun q => gTau q i j - gStar q i j) (inverseShearCoordinates q0 p)‖ ≤ e := by
    intro i j k hk
    have heq : (fun q => gTau q i j - test q i j) =ᶠ[𝓝 (inverseShearCoordinates q0 p)]
        (fun q => gTau q i j - gStar q i j) := by
      filter_upwards [metric_coeff_eventuallyEq hlocal i j] with q hq
      rw [hq]
    rw [← (heq.iteratedFDeriv ℝ k).self_of_nhds]
    exact happrox i j k hk
  have hfirst := actual_first_input_difference_le_full_jets hgTW hgSW hW hpW he hdiff
  rw [norm_sub_rev]
  exact actual_shear_first_jet_distance_le hgTW hgSW hW hq0 hpW hfirst

theorem metricApproximationAccuracy_le_inverse {tau : ℕ} (htau : 1 ≤ tau) :
    metricApproximationAccuracy tau ≤ 1 / (tau : ℝ) := by
  have htauR : (1 : ℝ) ≤ (tau : ℝ) := by exact_mod_cast htau
  have htauP : (0 : ℝ) < (tau : ℝ) := zero_lt_one.trans_le htauR
  unfold metricApproximationAccuracy
  exact one_div_le_one_div_of_le htauP (le_self_pow₀ htauR (Nat.ne_of_gt htau))

theorem exists_first_error_threshold {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ tau0 : ℕ, 1 ≤ tau0 ∧ ∀ tau : ℕ, tau0 ≤ tau →
      8 * metricApproximationAccuracy tau ≤ epsilon := by
  obtain ⟨n, hn⟩ := exists_nat_gt (8 / epsilon)
  refine ⟨max 1 n, le_max_left _ _, ?_⟩
  intro tau htau
  have htauN : 1 ≤ tau := (le_max_left _ _).trans htau
  have hnN : n ≤ tau := (le_max_right _ _).trans htau
  have htauR : (0 : ℝ) < (tau : ℝ) := zero_lt_one.trans_le (by exact_mod_cast htauN)
  have hnR : (n : ℝ) ≤ (tau : ℝ) := by exact_mod_cast hnN
  have hh : 8 < (n : ℝ) * epsilon := (div_lt_iff₀ he).mp hn
  have hb : 8 / (tau : ℝ) ≤ epsilon := (div_le_iff₀ htauR).mpr (by nlinarith)
  exact (mul_le_mul_of_nonneg_left (metricApproximationAccuracy_le_inverse htauN) (by norm_num)).trans
    (by simpa only [mul_one_div] using hb)

theorem actual_pulse_edge_reference_first_distance
    {gStar gTau : MetricField} {U V : Set Coord}
    (hgTau : SmoothPositiveOn gTau U) (hgStar : SmoothPositiveOn gStar V)
    (hU : IsOpen U) (hV : IsOpen V) {q0 a delta : ℝ} {N tau : ℕ}
    (hq0 : |q0| ≤ 1) (ha : 0 < a) (hd : 0 < delta) (htau : 1 ≤ tau)
    {x : ℝ}
    (hpU : inverseShearCoordinates q0 ![x, -delta / (tau : ℝ)] ∈ U)
    (hpV : inverseShearCoordinates q0 ![x, -delta / (tau : ℝ)] ∈ V)
    (happrox : ∀ i j : Fin 2, ∀ k ≤ tau,
      ‖iteratedFDeriv ℝ k
        (fun q => gTau q i j - testMetric gStar q0 a N delta (tau : ℝ) q i j)
        (inverseShearCoordinates q0 ![x, -delta / (tau : ℝ)])‖ ≤ metricApproximationAccuracy tau) :
    ‖actualCurvatureFirstInput (metricInShearCoordinates gStar q0) ![x, -delta / (tau : ℝ)] -
      actualCurvatureFirstInput (metricInShearCoordinates gTau q0) ![x, -delta / (tau : ℝ)]‖ ≤
      8 * metricApproximationAccuracy tau := by
  have htauR : (0 : ℝ) < (tau : ℝ) := zero_lt_one.trans_le (by exact_mod_cast htau)
  apply actual_sheared_reference_first_distance_of_locality hgTau hgStar hU hV hq0
    (metricApproximationAccuracy_pos htau).le hpU hpV
    (testMetric_eventuallyEq_below_pulse gStar q0 a N ha hd htauR le_rfl)
  intro i j k hk
  exact happrox i j k (hk.trans htau)

end SmoothLocal.Pulse

end

end OAI
