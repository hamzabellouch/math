import OAI.Geometry.IsometricImmersion.Comparison.ShearFirstJetComparison

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

def qPulseFirstJetBudget (a : ℝ) (ha : 0 < a) (N : ℕ) (delta tau : ℝ) : ℝ :=
  (8+scalarPulseFirstJetBound a ha delta)*tau/tau^N

theorem qPulseFirstJetBudget_nonneg {a : ℝ} (ha : 0 < a) (N : ℕ) (delta : ℝ)
    {tau : ℝ} (ht : 0 ≤ tau) : 0 ≤ qPulseFirstJetBudget a ha N delta tau :=
  div_nonneg (mul_nonneg (by linarith [scalarPulseFirstJetBound_nonneg ha delta]) ht)
    (pow_nonneg ht N)

theorem actual_sheared_first_jet_error_nat
    {gStar gTau : MetricField} {U : Set Coord} {q0 a delta : ℝ} {N n : ℕ}
    (hgStar : SmoothPositiveOn gStar U)
    (hgTest : SmoothPositiveOn (testMetric gStar q0 a N delta n) U)
    (hgTau : SmoothPositiveOn gTau U) (hU : IsOpen U)
    (hq : |q0| ≤ 1) (ha : 0 < a) (hN : 0 < N) (hn : 1 ≤ n) (hlarge : N-1 ≤ n)
    {p : Coord} (hp : inverseShearCoordinates q0 p ∈ U)
    (hjet : ‖actualCurvatureFirstInput gTau (inverseShearCoordinates q0 p)-
      actualCurvatureFirstInput (testMetric gStar q0 a N delta n)
        (inverseShearCoordinates q0 p)‖ ≤ 1/(n : ℝ)^n) :
    ‖actualCurvatureFirstInput (metricInShearCoordinates gTau q0) p-
      actualCurvatureFirstInput (metricInShearCoordinates gStar q0) p‖ ≤
      qPulseFirstJetBudget a ha N delta n := by
  have ht : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hfirst := actual_sheared_solution_first_jet_error hgStar hgTest hgTau hU hq ha ht hp hjet
  calc
    _ ≤ 8*(1/(n : ℝ)^n)+scalarPulseFirstJetBudget a ha N delta n := hfirst
    _ ≤ 8*((n : ℝ)/(n : ℝ)^N)+scalarPulseFirstJetBudget a ha N delta n :=
      add_le_add (mul_le_mul_of_nonneg_left
        (approximation_budget_le_pulse_error hN hn hlarge) (by norm_num : (0 : ℝ) ≤ 8)) le_rfl
    _ = _ := by unfold qPulseFirstJetBudget scalarPulseFirstJetBudget; ring

theorem qPulseFirstJetBudget_tendsto_zero {a : ℝ} (ha : 0 < a) (N : ℕ)
    (hN : 1 < N) (delta : ℝ) :
    Tendsto (qPulseFirstJetBudget a ha N delta) atTop (𝓝 0) := by
  have hn : N-1 ≠ 0 := by omega
  have hi := (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0)).pow (N-1)
  have h : Tendsto (fun t : ℝ => (8+scalarPulseFirstJetBound a ha delta)*(t⁻¹)^(N-1))
      atTop (𝓝 0) := by
    simpa only [zero_pow hn,mul_zero] using hi.const_mul (8+scalarPulseFirstJetBound a ha delta)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hN' : N = 1+(N-1) := by omega
  have hr : t/t^N = (t⁻¹)^(N-1) := by
    conv_lhs => rw [hN',pow_add,pow_one]
    rw [inv_pow]
    field_simp [ht.ne']
  simp only [qPulseFirstJetBudget,mul_div_assoc,hr]

theorem qPulseFirstJetBudget_eventual_margins (B H : ℝ) {d c a : ℝ}
    (hd : 0 < d) (hc : 0 < c) (ha : 0 < a) (N : ℕ) (hN : 1 < N)
    (delta : ℝ) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ tau : ℝ, T ≤ tau →
      qPulseFirstJetBudget a ha N delta tau ≤ 1 ∧
      (4*max B 0+2)*qPulseFirstJetBudget a ha N delta tau ≤ d/2 ∧
      H*qPulseFirstJetBudget a ha N delta tau ≤ c/2 := by
  have htend := qPulseFirstJetBudget_tendsto_zero ha N hN delta
  have h1 : ∀ᶠ t : ℝ in atTop, qPulseFirstJetBudget a ha N delta t < 1 :=
    htend.eventually (eventually_lt_nhds zero_lt_one)
  have hd' : Tendsto (fun t : ℝ => (4*max B 0+2)*qPulseFirstJetBudget a ha N delta t)
      atTop (𝓝 0) := by simpa only [mul_zero] using htend.const_mul (4*max B 0+2)
  have hc' : Tendsto (fun t : ℝ => H*qPulseFirstJetBudget a ha N delta t)
      atTop (𝓝 0) := by simpa only [mul_zero] using htend.const_mul H
  have hev : ∀ᶠ t : ℝ in atTop,
      qPulseFirstJetBudget a ha N delta t ≤ 1 ∧
      (4*max B 0+2)*qPulseFirstJetBudget a ha N delta t ≤ d/2 ∧
      H*qPulseFirstJetBudget a ha N delta t ≤ c/2 := by
    filter_upwards [h1,hd'.eventually (eventually_lt_nhds (half_pos hd)),
      hc'.eventually (eventually_lt_nhds (half_pos hc))] with t ht1 htd htc
    exact ⟨ht1.le,htd.le,htc.le⟩
  obtain ⟨T,hT⟩ := eventually_atTop.mp hev
  exact ⟨max T 1,le_max_right _ _,fun t ht => hT t ((le_max_left _ _).trans ht)⟩

end SmoothLocal.Pulse

end

end OAI
