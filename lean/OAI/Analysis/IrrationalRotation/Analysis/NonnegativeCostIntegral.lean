import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace OAI

open Filter MeasureTheory
open scoped ENNReal

namespace Invariant233

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem ae_summable_of_eventually_zero_off_point (u : ℕ → X → ℝ)
    (a : X) (ha : μ {a} = 0)
    (hfinite : ∀ x ≠ a, ∃ N : ℕ, ∀ n ≥ N, u n x = 0) :
    ∀ᵐ x ∂μ, Summable (fun n => u n x) := by
  have hne : ∀ᵐ x ∂μ, x ≠ a := by
    simpa only [ae_iff, not_not, Set.ofPred_eq_eq_singleton] using ha
  filter_upwards [hne] with x hx
  obtain ⟨N, hN⟩ := hfinite x hx
  apply summable_of_ne_finset_zero (s := Finset.range N)
  intro n hn
  exact hN n (Nat.le_of_not_gt (by simpa using hn))

theorem lintegral_ofReal_tsum_nonnegative (u : ℕ → X → ℝ)
    (hm : ∀ n, Measurable (u n)) (hu : ∀ n x, 0 ≤ u n x)
    (hs : ∀ᵐ x ∂μ, Summable (fun n => u n x)) :
    (∫⁻ x, ENNReal.ofReal (∑' n, u n x) ∂μ) =
      ∑' n, ∫⁻ x, ENNReal.ofReal (u n x) ∂μ := by
  calc
    (∫⁻ x, ENNReal.ofReal (∑' n, u n x) ∂μ) =
        ∫⁻ x, ∑' n, ENNReal.ofReal (u n x) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hs] with x hx
      exact ENNReal.ofReal_tsum_of_nonneg (fun n => hu n x) hx
    _ = _ := lintegral_tsum (fun n => (hm n).ennreal_ofReal.aemeasurable)

theorem lintegral_tsum_eq_top_of_block_lower_bound (u : ℕ → X → ℝ)
    (hm : ∀ n, Measurable (u n)) (hu : ∀ n x, 0 ≤ u n x)
    (hs : ∀ᵐ x ∂μ, Summable (fun n => u n x))
    (c : ℝ≥0∞) (hc : c ≠ 0)
    (hblock : ∀ n, c ≤ ∫⁻ x, ENNReal.ofReal (u n x) ∂μ) :
    (∫⁻ x, ENNReal.ofReal (∑' n, u n x) ∂μ) = ∞ := by
  rw [lintegral_ofReal_tsum_nonnegative u hm hu hs]
  apply top_unique
  calc
    ∞ = ∑' _ : ℕ, c := (ENNReal.tsum_const_eq_top_of_ne_zero hc).symm
    _ ≤ _ := ENNReal.tsum_le_tsum hblock

theorem lintegral_cost_add_background_eq_top (g b : X → ℝ)
    (hg : (∫⁻ x, ENNReal.ofReal (g x) ∂μ) = ∞)
    (hb : ∀ᵐ x ∂μ, 0 ≤ b x) :
    (∫⁻ x, ENNReal.ofReal (b x + g x) ∂μ) = ∞ := by
  apply top_unique
  rw [← hg]
  apply lintegral_mono_ae
  filter_upwards [hb] with x hx
  exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left hx)

theorem lintegral_relocated_background_eq_top
    (u : ℕ → X → ℝ) (b : X → ℝ) (a : X) (ha : μ {a} = 0)
    (hm : ∀ n, Measurable (u n)) (hu : ∀ n x, 0 ≤ u n x)
    (hfinite : ∀ x ≠ a, ∃ N : ℕ, ∀ n ≥ N, u n x = 0)
    (hb : ∀ᵐ x ∂μ, 0 ≤ b x)
    (c : ℝ≥0∞) (hc : c ≠ 0)
    (hblock : ∀ n, c ≤ ∫⁻ x, ENNReal.ofReal (u n x) ∂μ) :
    (∫⁻ x, ENNReal.ofReal (b x + ∑' n, u n x) ∂μ) = ∞ := by
  apply lintegral_cost_add_background_eq_top _ b _ hb
  exact lintegral_tsum_eq_top_of_block_lower_bound u hm hu
    (ae_summable_of_eventually_zero_off_point u a ha hfinite) c hc hblock

end Invariant233

end OAI
