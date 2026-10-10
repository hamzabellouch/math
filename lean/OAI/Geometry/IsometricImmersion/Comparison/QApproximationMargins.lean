import OAI.Geometry.IsometricImmersion.Comparison.QMetricApproximationInputs
import OAI.Geometry.IsometricImmersion.Pulses.PulseEdgeReferenceDistance

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

theorem actual_Q_approximation_eventual_margins (Bcompare BQ H : ℝ)
    {d dcompare c a : ℝ} (hd : 0 < d) (hdcompare : 0 < dcompare)
    (hc : 0 < c) (ha : 0 < a) (N : ℕ) (hN : 1 < N) (delta : ℝ) :
    ∀ᶠ tau : ℕ in atTop,
      2 ≤ tau ∧ N ≤ tau ∧
      0 ≤ metricApproximationAccuracy tau ∧ metricApproximationAccuracy tau ≤ 1 ∧
      (4*max Bcompare 0+2)*metricApproximationAccuracy tau ≤ dcompare/2 ∧
      metricApproximationAccuracy tau ≤ (tau : ℝ)/(tau : ℝ)^N ∧
      0 ≤ qPulseFirstJetBudget a ha N delta (tau : ℝ) ∧
      qPulseFirstJetBudget a ha N delta (tau : ℝ) ≤ 1 ∧
      (4*max BQ 0+2)*qPulseFirstJetBudget a ha N delta (tau : ℝ) ≤ d/2 ∧
      H*qPulseFirstJetBudget a ha N delta (tau : ℝ) ≤ c/2 := by
  let K := 4*max Bcompare 0+2
  have hK : 0 < K := by dsimp only [K]; have hh := le_max_right Bcompare 0; linarith
  let epsilon := min 1 (dcompare/(2*K))
  have he : 0 < epsilon := lt_min (by norm_num) (div_pos hdcompare (by positivity))
  obtain ⟨tau0,_,haccurate⟩ := exists_first_error_threshold (by positivity : 0 < 8*epsilon)
  obtain ⟨T,_,hQ⟩ := qPulseFirstJetBudget_eventual_margins BQ H hd hc ha N hN delta
  have hlarge : ∀ᶠ tau : ℕ in atTop, T ≤ (tau : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop T)
  filter_upwards [eventually_ge_atTop tau0,eventually_ge_atTop 2,eventually_ge_atTop N,hlarge]
    with tau ht0 ht2 htN ht
  have ht1 : 1 ≤ tau := by omega
  have htpos : (0 : ℝ) < tau := zero_lt_one.trans_le (by exact_mod_cast ht1)
  have herr : metricApproximationAccuracy tau ≤ epsilon := by linarith [haccurate tau ht0]
  have hsmall : K*metricApproximationAccuracy tau ≤ dcompare/2 := by
    have heK : epsilon ≤ dcompare/(2*K) := min_le_right _ _
    have hh := (le_div_iff₀ (show 0 < 2*K by positivity)).mp (herr.trans heK)
    nlinarith
  exact ⟨ht2,htN,(metricApproximationAccuracy_pos (by omega)).le,
    herr.trans (min_le_left _ _),hsmall,
    approximation_budget_le_pulse_error (by omega) ht1 (by omega),
    qPulseFirstJetBudget_nonneg ha N delta htpos.le,(hQ _ ht).1,(hQ _ ht).2.1,(hQ _ ht).2.2⟩

end SmoothLocal.Pulse

end

end OAI
