import OAI.Geometry.IsometricImmersion.Estimates.ActualQMomentLower
import OAI.Geometry.IsometricImmersion.Pulses.QPulseFirstJetBudget

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

def qMomentErrorCoefficient (A Cfirst Ctest Ccompare a : ℝ) (ha : 0 < a) (delta : ℝ) : ℝ :=
  2*A*(testDensityErrorCoefficient Ctest a ha delta+Ccompare)+
    Cfirst*(8+scalarPulseFirstJetBound a ha delta)

theorem qMomentErrorCoefficient_nonneg {A Cfirst Ctest Ccompare a : ℝ} (ha : 0 < a)
    (hA : 0 ≤ A) (hCf : 0 ≤ Cfirst) (hCt : 0 ≤ Ctest) (hCc : 0 ≤ Ccompare) (delta : ℝ) :
    0 ≤ qMomentErrorCoefficient A Cfirst Ctest Ccompare a ha delta := by
  have hCd : 0 ≤ testDensityErrorCoefficient Ctest a ha delta :=
    add_nonneg (pulsePrincipalRemainderBound_nonneg a ha)
      (mul_nonneg hCt (scalarPulseFirstJetBound_nonneg ha delta))
  unfold qMomentErrorCoefficient
  exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA) (add_nonneg hCd hCc))
    (mul_nonneg hCf (add_nonneg (by norm_num) (scalarPulseFirstJetBound_nonneg ha delta)))

theorem qForcingRemainderBudget_le_first_scale
    {A Cfirst Ctest Ccompare a delta tau epsilon epsilonQ : ℝ} {N : ℕ} (ha : 0 < a)
    (hA : 0 ≤ A) (hCf : 0 ≤ Cfirst) (hCc : 0 ≤ Ccompare)
    (he : epsilon ≤ tau/tau^N) (heQ : epsilonQ ≤ qPulseFirstJetBudget a ha N delta tau) :
    qForcingRemainderBudget A Cfirst Ctest Ccompare a ha N delta tau epsilon epsilonQ ≤
      qMomentErrorCoefficient A Cfirst Ctest Ccompare a ha delta*tau/tau^N := by
  unfold qForcingRemainderBudget
  calc
    _ ≤ 2*A*(testDensityErrorCoefficient Ctest a ha delta*tau/tau^N+Ccompare*(tau/tau^N))+
        Cfirst*qPulseFirstJetBudget a ha N delta tau :=
      add_le_add (mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left he hCc)) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hA))
        (mul_le_mul_of_nonneg_left heQ hCf)
    _ = _ := by unfold qMomentErrorCoefficient qPulseFirstJetBudget; ring

theorem qMoment_budget_absorption_threshold
    {A Cfirst Ctest Ccompare a c3 : ℝ} (ha : 0 < a) (hc3 : 0 < c3)
    (hA : 0 ≤ A) (hCf : 0 ≤ Cfirst) (hCt : 0 ≤ Ctest) (hCc : 0 ≤ Ccompare)
    (N : ℕ) (delta : ℝ) (hdelta : 0 ≤ delta) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ tau : ℝ, T ≤ tau → ∀ epsilon epsilonQ : ℝ,
      epsilon ≤ tau/tau^N → epsilonQ ≤ qPulseFirstJetBudget a ha N delta tau →
      qForcingRemainderBudget A Cfirst Ctest Ccompare a ha N delta tau epsilon epsilonQ*
        (2*delta/tau)*(∫ x : ℝ, axisBump a x) ≤ (c3/2)*delta*tau/tau^N := by
  let K := qMomentErrorCoefficient A Cfirst Ctest Ccompare a ha delta
  let I := ∫ x : ℝ, axisBump a x
  have hK : 0 ≤ K := qMomentErrorCoefficient_nonneg ha hA hCf hCt hCc delta
  have hI : 0 ≤ I := (axisBump_integral_pos ha).le
  refine ⟨max 1 (4*K*I/c3),le_max_left _ _,?_⟩
  intro tau ht epsilon epsilonQ he heQ
  have ht1 : 1 ≤ tau := (le_max_left _ _).trans ht
  have htpos : 0 < tau := zero_lt_one.trans_le ht1
  have hthreshold : 4*K*I/c3 ≤ tau := (le_max_right _ _).trans ht
  have hcoeff : 2*K*I ≤ (c3/2)*tau := by
    have hh := (div_le_iff₀ hc3).mp hthreshold
    nlinarith
  have hB := qForcingRemainderBudget_le_first_scale (Ctest := Ctest) ha hA hCf hCc he heQ
  have hwidth : 0 ≤ 2*delta/tau := div_nonneg (mul_nonneg (by norm_num) hdelta) htpos.le
  have hscale : 0 ≤ delta/tau^N := div_nonneg hdelta (pow_nonneg htpos.le N)
  calc
    _ ≤ (K*tau/tau^N)*(2*delta/tau)*I :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hB hwidth) hI
    _ = (2*K*I)*(delta/tau^N) := by field_simp [htpos.ne']
    _ ≤ ((c3/2)*tau)*(delta/tau^N) := mul_le_mul_of_nonneg_right hcoeff hscale
    _ = _ := by ring

end SmoothLocal.Pulse

end

end OAI
