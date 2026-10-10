import Mathlib

namespace OAI

/-! The final arithmetic-progression telescoping step in the cavity lower
bound, with an eventual increment bound and the actual terminal dimension. -/

noncomputable section
open Filter
open scoped Topology

namespace InvariantIsing

theorem cavity_progression_pressure_lower (A : ℕ → ℝ) (N₀ step L : ℝ)
    (hN₀ : 0 < N₀) (hstep : 0 < step)
    (hinc : ∀ ε > 0, ∀ᶠ n in atTop, step * (L - ε) ≤ A (n + 1) - A n) :
    ∀ ε > 0, ∀ᶠ n in atTop, L - ε ≤ A n / (N₀ + step * n) := by
  intro ε hε
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hinc (ε / 2) (half_pos hε))
  have hlower : ∀ n, M ≤ n → A M + ((n : ℝ) - M) * step * (L - ε / 2) ≤ A n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      have hi := hM n hn
      push_cast
      nlinarith
  let D := A M - (M : ℝ) * step * (L - ε / 2) - N₀ * (L - ε)
  have hb : 0 < step * (ε / 2) := mul_pos hstep (half_pos hε)
  have hcast := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
    (eventually_ge_atTop (-D / (step * (ε / 2))))
  filter_upwards [eventually_ge_atTop M, hcast] with n hn hlarge
  have hden : 0 < N₀ + step * n := add_pos_of_pos_of_nonneg hN₀ (by positivity)
  apply (le_div_iff₀ hden).mpr
  have hmul := (div_le_iff₀ hb).mp hlarge
  have ha := hlower n hn
  dsimp only [D] at hmul
  nlinarith

end InvariantIsing

end

end OAI
