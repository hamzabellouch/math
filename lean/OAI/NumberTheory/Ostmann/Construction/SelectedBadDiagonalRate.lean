import OAI.NumberTheory.Ostmann.Arithmetic.MovingBadDiagonalRate
import OAI.NumberTheory.Ostmann.Construction.WholeShellRetainedLinearMass
import OAI.NumberTheory.Ostmann.Construction.HarmonicFamilyBounds

namespace OAI

/-! # The bad diagonal rate for the actual selected prime sets -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem selected_prime_mass_exp_lower (c K L : ℝ) (hc : 0 < c)
    (hL : max 1 (-Real.log c) ≤ L) (Q : Finset ℕ)
    (hmass : c / Real.exp (K * L) ≤ ∑ q ∈ Q, (q : ℝ)⁻¹) :
    Real.exp (-(K + 1) * L) ≤ ∑ q ∈ Q, (q : ℝ)⁻¹ := by
  obtain ⟨hp, hi⟩ := selected_cell_normalizer c K L _ hc hL hmass
  have h := inv_anti₀ (inv_pos.mpr hp) hi
  simpa only [inv_inv, ← Real.exp_neg, neg_mul] using h

theorem selected_bad_diagonal_rate {CM : ℝ} (hM : MertensEstimate CM)
    (n s k : ℕ) (hk : 0 < k) (c K Bs BD Bz B ε εdiag : ℝ)
    (hc : 0 < c) (hK : 0 ≤ K) (hε : 0 < ε) (hεdiag : 0 ≤ εdiag)
    (hbudget : 4 * (K + 1) * s ≤ ε * (k : ℝ) ^ 4) (hBz : 9 ≤ Bz)
    (hBD : Bs + 2 * B +
      (Real.log 2 - Real.log (1 / 16000 : ℝ) + 5 / 4 + ε + Real.log 12 + 1 + εdiag) + 6 ≤ BD) :
    ∀ᶠ L : ℝ in atTop, let m := spectatorBulkCount k L
      let z := (k : ℝ) ^ 4
      let r : ℝ := (2 ^ n : ℕ)
      let Δ := spectatorBaseGap Bs z m
      ∀ (global : Finset ℕ) (Q : MovingRegularSlot n s m → Finset ℕ),
      (global.card : ℝ) ≤ Real.exp ((K + 1) * L) →
      (∀ j, Q (movingTemplateBulk n s m j) =
        primeLogCellSet 1 0 (Real.exp ((4 / 1000 : ℝ) * L))
          (Real.exp ((6 / 1000 : ℝ) * L)) \ global) →
      (∀ j, c / Real.exp (K * L) ≤ ∑ q ∈ Q j, (q : ℝ)⁻¹) →
      ∀ arch : ℝ, arch ≤ Real.exp (-spectatorStepGap BD Bz z r m) →
      arch *
        (((((2 ^ n + 1) * (2 ^ n) ^ (2 * 2 ^ n) : ℕ) : ℝ) *
          Real.exp (r * m * (-(3 / 4 : ℝ) * Real.log r + 5 / 4))) *
            (((Fintype.card (MovingRegularSlot n s m)).factorial : ℝ) *
              (∏ i, (∑ q ∈ Q i, (q : ℝ)⁻¹)⁻¹))) *
        Real.exp (r * Δ + (Real.log 12 + 1) * r * m + εdiag * m) ≤
          Real.exp (-(2 * B + 6) * r * m) := by
  filter_upwards [eventual_moving_bad_diagonal_rate n s k hk Bs BD Bz B (K + 1)
    (1 / 16000) ε εdiag (by norm_num) hε hεdiag hbudget hBz hBD,
    whole_shell_retained_linear_mass hM (K + 1) (by linarith),
    eventually_ge_atTop (max 1 (-Real.log c))] with L hbad hbulk hL
  dsimp only at hbad ⊢
  intro global Q hglobal hQ hmass arch harch
  apply hbad (fun i => ∑ q ∈ Q i, (q : ℝ)⁻¹)
  · intro j
    exact selected_prime_mass_exp_lower c K L hc hL _ (hmass _)
  · intro j
    change (1 / 16000 : ℝ) * L ≤ ∑ q ∈ Q (movingTemplateBulk n s (spectatorBulkCount k L) j), (q : ℝ)⁻¹
    rw [hQ j]
    convert hbulk global hglobal using 1; ring
  · exact harch

end Ostmann

end OAI
