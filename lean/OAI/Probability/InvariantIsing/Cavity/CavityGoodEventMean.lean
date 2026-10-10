import Mathlib

namespace OAI

/-! Averaging the cavity lower bound over good perturbation parameters.
The complement is controlled by the uniform finite-volume lower bound. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace InvariantIsing

theorem cavity_good_event_mean_lower
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (G : (n : ℕ) → Set (Ω n)) (hG : ∀ n, MeasurableSet (G n))
    (f : (n : ℕ) → Ω n → ℝ) (hf : ∀ n, Integrable (f n) (P n))
    (L B : ℝ) (hlower : ∀ n ω, B ≤ f n ω)
    (hmass : Tendsto (fun n => (P n).real (G n)) atTop (𝓝 1))
    (hgood : ∀ ε > 0, ∀ᶠ n in atTop, ∀ ω ∈ G n, L - ε ≤ f n ω) :
    ∀ ε > 0, ∀ᶠ n in atTop, L - ε ≤ ∫ ω, f n ω ∂P n := by
  intro ε hε
  have hlim : Tendsto (fun n => B + (L - ε / 2 - B) * (P n).real (G n))
      atTop (𝓝 (L - ε / 2)) := by
    simpa only [mul_one, add_sub_cancel] using
      (hmass.const_mul (L - ε / 2 - B)).const_add B
  have hnear := hlim.eventually (lt_mem_nhds (show L - ε < L - ε / 2 by linarith))
  filter_upwards [hgood (ε / 2) (half_pos hε), hnear] with n hn hclose
  have hi : Integrable (fun ω => B + (L - ε / 2 - B) *
      (G n).indicator (fun _ => (1 : ℝ)) ω) (P n) :=
    (integrable_const B).add (((integrable_const (1 : ℝ)).indicator (hG n)).const_mul _)
  have hb : (∫ ω, B + (L - ε / 2 - B) *
      (G n).indicator (fun _ => (1 : ℝ)) ω ∂P n) ≤ ∫ ω, f n ω ∂P n := by
    apply integral_mono hi (hf n)
    intro ω
    by_cases hω : ω ∈ G n
    · simpa only [indicator_of_mem hω, mul_one, add_sub_cancel] using hn ω hω
    · simpa only [indicator_of_notMem hω, mul_zero, add_zero] using hlower n ω
  have he : (∫ ω, B + (L - ε / 2 - B) *
      (G n).indicator (fun _ => (1 : ℝ)) ω ∂P n) =
      B + (L - ε / 2 - B) * (P n).real (G n) := by
    rw [integral_add (integrable_const B)
      (((integrable_const (1 : ℝ)).indicator (hG n)).const_mul _), integral_const_mul,
      integral_indicator (hG n)]
    simp
  rw [he] at hb
  exact hclose.le.trans hb

end InvariantIsing

end

end OAI
