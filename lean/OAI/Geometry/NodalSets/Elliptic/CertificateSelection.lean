import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Tactic.Linarith

namespace OAI

namespace Yau
open MeasureTheory Set
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem bad_event_integral_bound {Z : Ω → ℝ} {Q : Set Ω} {T : ℝ}
    (hZ : Integrable Z μ) (hbound : ∀ w, Z w ≤ T) :
    (∫ w in Qᶜ, Z w ∂μ) ≤ (μ Qᶜ).toReal * T := by
  have h := integral_mono hZ.integrableOn (integrable_const T :
    Integrable (fun _ : Ω ↦ T) (μ.restrict Qᶜ)) hbound
  simpa [Measure.real, smul_eq_mul] using h

theorem exists_good_certificate_weight {Z : Ω → ℝ} {Q : Set Ω} {T c : ℝ}
    (hZ : Integrable Z μ) (hQ : MeasurableSet Q)
    (hT : 0 < T) (hc : 0 < c) (hbound : ∀ w, Z w ≤ T)
    (hexpect : c * T ≤ ∫ w, Z w ∂μ) (hfail : (μ Qᶜ).toReal < c / 2) :
    ∃ w ∈ Q, c * T / 2 ≤ Z w := by
  have hbad := bad_event_integral_bound (Q := Q) hZ hbound
  have hsplit := integral_add_compl hQ hZ
  have hgood : c * T / 2 < ∫ w in Q, Z w ∂μ := by
    have hm := mul_lt_mul_of_pos_right hfail hT
    nlinarith
  by_contra hn
  push Not at hn
  have hp : ∀ w, Q.indicator Z w ≤ c * T / 2 := by
    intro w
    by_cases hw : w ∈ Q
    · simpa [hw] using (hn w hw).le
    · simp only [indicator_of_notMem hw]
      positivity
  have hupper := integral_mono (hZ.indicator hQ)
    (integrable_const (c * T / 2) : Integrable (fun _ : Ω ↦ c * T / 2) μ) hp
  rw [integral_indicator hQ] at hupper
  have hupper' : (∫ w in Q, Z w ∂μ) ≤ c * T / 2 := by simpa using hupper
  exact (not_lt_of_ge hupper') hgood

end
end Yau

end OAI
