import OAI.Analysis.CircleDomains.Topology.ComponentControl

namespace OAI

/-!
# Simultaneous choice of small random quantities

The finite-transfer grid selection needs one sample for which both the wedge
integral and terminal count are small, while retaining the conull compatibility
conditions. The proof below uses the integral of the sum of the two normalized
quantities, so its conclusion preserves any specified conull event.
-/

open MeasureTheory Filter

namespace CircleDomainRigidity.FiniteTransfer

/-- Two nonnegative integrable costs can simultaneously be kept below their
thresholds when the sum of their normalized expectations is below one. -/
theorem exists_good_sample {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {f g : X → ℝ} {P : X → Prop} {A B : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) (hP : ∀ᵐ x ∂μ, P x)
    (hmean : (∫ x, f x ∂μ) / A + (∫ x, g x ∂μ) / B < 1) :
    ∃ x, P x ∧ f x < A ∧ g x < B := by
  by_contra hgood
  have hi := (hf.div_const A).add (hg.div_const B)
  have hpoint : ∀ᵐ x ∂μ, (1 : ℝ) ≤ f x / A + g x / B := by
    filter_upwards [hf0, hg0, hP] with x hfx hgx hPx
    have hfa : 0 ≤ f x / A := div_nonneg hfx hA.le
    have hgb : 0 ≤ g x / B := div_nonneg hgx hB.le
    rcases lt_or_ge (f x) A with hlt | hge
    · have hgB : B ≤ g x := le_of_not_gt fun hltg => hgood ⟨x, hPx, hlt, hltg⟩
      have hh : 1 ≤ g x / B := (le_div_iff₀ hB).mpr (by simpa using hgB)
      linarith
    · have hh : 1 ≤ f x / A := (le_div_iff₀ hA).mpr (by simpa using hge)
      linarith
  have hbound := integral_mono_ae (integrable_const (1 : ℝ)) hi hpoint
  simp only [Pi.add_apply] at hbound
  rw [integral_add (hf.div_const A) (hg.div_const B), integral_div, integral_div] at hbound
  have hge : (1 : ℝ) ≤ (∫ x, f x ∂μ) / A + (∫ x, g x ∂μ) / B := by
    simpa using hbound
  exact (not_lt_of_ge hge) hmean

end CircleDomainRigidity.FiniteTransfer

end OAI
