import OAI.NumberTheory.JointDickman.Analysis.MellinPrefixBound
import OAI.NumberTheory.JointDickman.Amplification.UniformPrefixLimit

namespace OAI

/-! # The low-frequency consequence of ordinary marginal prefix means -/
namespace JointDickman
open Finset Filter
open scoped Topology

/-- Uniformity over a fixed bounded frequency range follows from marginal
means alone. Multiplicativity is needed only for the remaining frequencies. -/
theorem angularMellin_uniform_bounded_frequency (f : ℝ → ℕ → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ x n, ‖f x n‖ ≤ C) (hf0 : ∀ x, f x 0 = 0)
    (hmean : ∀ A : ℝ, 0 < A → Tendsto
      (fun x : ℝ => (∑ n ∈ Ioc 0 ⌊A * x⌋₊, f x n) / (x : ℂ)) atTop (𝓝 0))
    {A T ε : ℝ} (hA : 0 < A) (hT : 0 ≤ T) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ t : ℝ, |t| ≤ T →
      ‖angularMellinPolynomial (Ioc ⌊A * x⌋₊ ⌊4 * (A * x)⌋₊) (f x) t‖ ≤ ε := by
  let δ := ε * A / (5 + 3 * T)
  have hden : 0 < 5 + 3 * T := by linarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hpref := uniform_prefix_of_marginal_means f hC hf hmean (4 * A) (by positivity) hδ
  filter_upwards [hpref, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  intro t ht
  have hAx : 0 < A * x := mul_pos hA hx0
  have hprefix (u : ℝ) (hu : u ∈ Set.Icc (A * x) (4 * (A * x))) :
      ‖∑ n ∈ Icc 0 ⌊u⌋₊, f x n‖ ≤ δ * x := by
    have he : (∑ n ∈ Icc 0 ⌊u⌋₊, f x n) = ∑ n ∈ Ioc 0 ⌊u⌋₊, f x n := by
      rw [← Ioc_insert_left (Nat.zero_le ⌊u⌋₊), sum_insert (by simp), hf0, zero_add]
    rw [he]
    exact hx u ⟨hAx.le.trans hu.1, by nlinarith [hu.2]⟩
  have hb := angularMellinPolynomial_le_of_prefix (f x) hAx hT (mul_nonneg hδ.le hx0.le) ht hprefix
  apply hb.trans_eq
  dsimp [δ]
  field_simp

end JointDickman

end OAI
