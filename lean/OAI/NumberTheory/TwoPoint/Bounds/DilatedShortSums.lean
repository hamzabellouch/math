import OAI.NumberTheory.TwoPoint.Bounds.DilationMRT
import OAI.NumberTheory.TwoPoint.Bounds.SmoothWindowBound

namespace OAI

/-! The published MRT input applied to the actual sequence f(qn), using
only the exact smooth-divisor expansion. All dilation dependence is exposed
through one Euler product and an elementary finite truncation error. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem MRTShortExponentialInput.dilated_short_sums
    (hMRT : MRTShortExponentialInput) {f : ℕ → ℂ}
    (hfnp : UniformlyNonpretentious f) (hf : OneBounded f) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset ℕ) (q D K : ℕ),
      0 < q → 0 < K → K ≤ D →
      (∀ a ∈ Icc 1 K, 10 ≤ D / a + 1) →
      ∀ E : ℝ, 0 ≤ E →
      (∀ a ∈ Icc 1 K,
        Real.log (Real.log (D / a + 1 : ℕ)) / Real.log (D / a + 1 : ℕ) ≤ E) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ Y : ℕ in atTop,
        ∀ b : ℕ → ℂ, Multiplicative b → OneBounded b →
        (∀ p, Nat.Prime p → p ∉ P → b p = f p) → ∀ α : ℝ,
        (∑ v ∈ range Y, ‖shortWindowSum (fun n => b (q * n)) D α v‖) ≤
          (D : ℝ) * Y *
            ((4 * C * (E + ε) + 2 * (K : ℝ) ^ (-(1 / 2) : ℝ)) *
              smoothReciprocalProduct q.primeFactors (1 / 2 : ℝ)) + K * Y := by
  obtain ⟨C, hC, hquotient⟩ := hMRT.modified_quotient_windows hfnp hf
  refine ⟨C, hC, ?_⟩
  intro P q D K hq hK hKD hlength E hE hlog ε hε
  filter_upwards [hquotient P q D K hq hlength ε hε,
    eventually_ge_atTop D] with Y hY hDY
  intro b hb hbb heq α
  have hbase : ∀ a ∈ Icc 1 K, ∀ β : ℝ,
      (∑ m ∈ range (Y / a + 1),
        ‖shortWindowSum (coprimeRestriction q b) (D / a + 1) β m‖) ≤
        C * (D / a + 1 : ℕ) * (Y / a + 1 : ℕ) * (E + ε) := by
    intro a ha β
    exact (hY b hb hbb heq a ha β).trans
      (mul_le_mul_of_nonneg_left (add_le_add (hlog a ha) le_rfl) (by positivity))
  exact (smooth_dilation_window_bound hb hbb q K D Y hq hK hKD hDY C (E + ε)
    hC.le (by positivity) hbase α).trans_eq (by ring)

end TwoPointCorrelations

end OAI
