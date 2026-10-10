import OAI.Analysis.CircleDomains.Selection.GoodSample
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

namespace OAI

/-!
# One compatible sample with arbitrarily late good widths

The grid shifts must be fixed before the staircase width is chosen.
Fatou's lemma preserves a strict expected-cost budget along a sequence
of widths, and yields infinitely many good widths for one fixed sample.
-/

open MeasureTheory Filter
open scoped ENNReal

namespace CircleDomainRigidity.FiniteTransfer

theorem exists_compatible_frequently_small_cost
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    (F : ℕ → X → ℝ≥0∞) (hF : ∀ n, AEMeasurable (F n) μ)
    {P : X → Prop} (hP : ∀ᵐ x ∂μ, P x) {c : ℝ≥0∞} (hc : c < 1)
    (hmean : ∀ n, (∫⁻ x, F n x ∂μ) ≤ c) :
    ∃ x, P x ∧ ∃ᶠ n in atTop, F n x < 1 := by
  have hlim : (∫⁻ x, liminf (fun n => F n x) atTop ∂μ) ≤ c := by
    apply (lintegral_liminf_le' hF).trans
    exact liminf_le_of_frequently_le' (Frequently.of_forall hmean)
  have hgood : ∃ x, P x ∧ liminf (fun n => F n x) atTop < 1 := by
    by_contra hno
    push Not at hno
    have hpoint : ∀ᵐ x ∂μ, (1 : ℝ≥0∞) ≤ liminf (fun n => F n x) atTop :=
      hP.mono (fun x hx => hno x hx)
    have hge := lintegral_mono_ae hpoint
    have hge' : (1 : ℝ≥0∞) ≤ ∫⁻ x, liminf (fun n => F n x) atTop ∂μ := by
      simpa using hge
    exact (not_lt_of_ge (hge'.trans hlim)) hc
  obtain ⟨x, hx, hsmall⟩ := hgood
  exact ⟨x, hx, frequently_lt_of_liminf_lt (by isBoundedDefault) hsmall⟩

/-- The second cost is independent of the width, so the same sample
has a small terminal cost and arbitrarily late small wedge costs. -/
theorem exists_compatible_frequently_small_pair
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    (W : ℕ → X → ℝ≥0∞) (J : X → ℝ≥0∞)
    (hW : ∀ n, AEMeasurable (W n) μ) (hJ : AEMeasurable J μ)
    {P : X → Prop} (hP : ∀ᵐ x ∂μ, P x) {c : ℝ≥0∞} (hc : c < 1)
    (hmean : ∀ n, (∫⁻ x, W n x + J x ∂μ) ≤ c) :
    ∃ x, P x ∧ J x < 1 ∧ ∃ᶠ n in atTop, W n x < 1 := by
  obtain ⟨x, hx, hgood⟩ := exists_compatible_frequently_small_cost
    (fun n x => W n x + J x) (fun n => (hW n).add hJ) hP hc hmean
  obtain ⟨n, hn⟩ := hgood.exists
  refine ⟨x, hx, (le_add_left le_rfl).trans_lt hn, ?_⟩
  exact hgood.mono (fun n hn => (le_add_right le_rfl).trans_lt hn)

end CircleDomainRigidity.FiniteTransfer

end OAI
