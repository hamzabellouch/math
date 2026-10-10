import OAI.NumberTheory.EgyptianFractions.DeterministicMean
import OAI.NumberTheory.EgyptianFractions.DeterministicMeanDecay

namespace OAI
noncomputable section
open scoped BigOperators
open Filter
namespace Problem337

/-- The deterministic high-level Fourier second moment, at the exact
exponential rate used by the residue exceptional-set construction.
The threshold is uniform in the scale, cutoff, frequency, and indexed list. -/
theorem deterministic_mean_bound (D : ℝ) (hD : 255 ≤ D) :
    ∀ᶠ S : ℝ in atTop, ∀ (m X C ell : ℝ),
      S / (2 * Real.log S) ≤ m → m ≤ S / Real.log S →
      Real.exp S ≤ X → X ≤ Real.exp (D * S / 4) →
      Real.exp (D * S) ≤ C → C ≤ Real.exp (2 * D * S) →
      1 ≤ ell → ell ≤ Real.exp (m / 2500) →
      ∀ {β : Type*} (T : Finset β) (t : β → ℕ),
        Set.InjOn t (T : Set β) →
        Real.exp (Real.log 2 * m) ≤ (T.card : ℝ) →
        (∀ i ∈ T, (t i : ℝ) ≤ Real.exp (101 * S)) →
        (∑ u ∈ Finset.Icc (⌊Real.exp (-m / 10000) * X⌋₊ + 1) ⌊X⌋₊,
          ‖(∑ i ∈ T, differencingPhase (ell * C * (t i : ℝ) / (u : ℝ))) /
            (T.card : ℂ)‖ ^ 2) ≤ X * Real.exp (-m / 100) := by
  obtain ⟨A, c, hA, hc, hmean⟩ := deterministic_mean_two_errors D hD
  have hlog : (1 / 100 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  filter_upwards [hmean,
    ResidueLevels.eventually_exp_absorb_real_scale
      (a := 1 / 100) (b := Real.log 2) (c := c) (C := A) hlog hc hA.le,
    eventually_ge_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))]
    with S hmean hdecay hS hlogS
  intro m X C ell hmlo hmhi hXlo hXhi hClo hChi hell hellhi β T t ht hcard hsize
  have hmS : m ≤ S := hmhi.trans (div_le_self hS hlogS)
  have hX : 0 ≤ X := (Real.exp_pos S).le.trans hXlo
  apply (hmean m X C ell hmS hXlo hXhi hClo hChi hell hellhi T t ht hcard hsize).trans
  have h := mul_le_mul_of_nonneg_left (hdecay m hmlo hmhi) hX
  simpa only [show -(1 / 100 : ℝ) * m = -m / 100 by ring] using h

end Problem337

end

end OAI
