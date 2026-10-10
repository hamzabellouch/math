import OAI.MeasureTheory.Falconer.Recursion.Entry
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

/-!
# Dimension-dependent normalization and branch ledger

The critical slope is `d / 2`. Both copies of a profile are needed for
the cancellation of the spatial normalization. The last-potential bound
uses the last interval with a defined two-depth potential, even when the
final interval itself is shorter.
-/

namespace Falconer
open scoped BigOperators

theorem dyadic_rpow_change_base {N : ℕ} (hN : 0 < N) (x : ℝ) :
    ((2 : ℝ)^N) ^ (x / (N : ℝ)) = (2 : ℝ)^x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- Equation `rec:normalization`, in every dimension. -/
theorem critical_profile_normalization {N : ℕ} (hN : 0 < N)
    (d a b Δ : ℝ) :
    (2 : ℝ)^(d * (b-a)) * ((2 : ℝ)^N)^(-2 * (Δ + (d/2) * (b-a) / N)) =
      ((2 : ℝ)^N)^(-2 * Δ) := by
  rw [← dyadic_rpow_change_base hN (d * (b-a)),
    ← Real.rpow_add (by positivity : (0 : ℝ) < (2 : ℝ)^N)]
  congr 1
  ring

/-- The product of split weights, child counts and prefactor ratio in
`graph:bound`. Losses remain explicit and the two profile increments cancel
the entire critical spatial exponent. -/
theorem two_profile_graph_normalization {N : ℕ} (hN : 0 < N)
    (d a p Δ₁ Δ₂ countLoss degree : ℝ)
    (I₁ I₂ : ℝ)
    (hI₁ : I₁ = Δ₁ + (d/2) * (p-a) / N)
    (hI₂ : I₂ = Δ₂ + (d/2) * (p-a) / N) :
    ((2 : ℝ)^N)^(-2 * (I₁+I₂)) * ((2 : ℝ)^N)^(I₁+I₂+countLoss) *
        (2 : ℝ)^(d * (p-a)) * ((2 : ℝ)^N)^degree =
      ((2 : ℝ)^N)^(-Δ₁-Δ₂+countLoss+degree) := by
  rw [← dyadic_rpow_change_base hN (d * (p-a))]
  rw [← Real.rpow_add (by positivity : (0 : ℝ) < (2 : ℝ)^N),
    ← Real.rpow_add (by positivity : (0 : ℝ) < (2 : ℝ)^N),
    ← Real.rpow_add (by positivity : (0 : ℝ) < (2 : ℝ)^N)]
  rw [hI₁, hI₂]
  congr 1
  ring

/-- The last defined two-depth potential is controlled by the final start.
Only the diameter `Q` of the two chosen nearby depths enters the loss. -/
theorem last_potential_bound (A : ℕ → ℝ) {u w f Q N : ℕ} {d : ℝ}
    (hQ : 0 < Q) (hwidth : u + Q ≤ w) (huf : u ≤ f) (hfw : f ≤ w)
    (hd : 0 ≤ d) (hN : 0 < N)
    (hlip : ∀ i, u ≤ i → i ≤ w →
      |A i - A f| ≤ d * |(i : ℝ) - f| / N) :
    PlanarFalconer.potential A u w Q ≤ 2 * A f + 2 * d * Q / N := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hlocal : ∀ i, u ≤ i → i ≤ w → i ≤ f + Q → f ≤ i + Q →
      A i ≤ A f + d * Q / N := by
    intro i hui hiw hif hfi
    have hif' : (i : ℝ) ≤ f + Q := by exact_mod_cast hif
    have hfi' : (f : ℝ) ≤ i + Q := by exact_mod_cast hfi
    have habs : |(i : ℝ) - f| ≤ Q := abs_le.mpr ⟨by linarith, by linarith⟩
    have hb := (hlip i hui hiw).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left habs hd) hNr.le)
    linarith [(abs_le.mp hb).2]
  have hh := PlanarFalconer.potential_near_final A hQ hwidth huf hfw hlocal
  convert hh using 1
  ring

/-- Dimension-dependent branch exponent after exact telescoping, payment
of all graph costs, and the final Lipschitz potential estimate. -/
theorem branch_exponent_of_lipschitz (A : ℕ → ℝ) (start : ℕ → ℕ)
    (V cost loss : ℕ → ℝ) (n : ℕ) {u w Q N : ℕ} {d : ℝ}
    (terminal lossBound : ℝ)
    (hpay : ∀ k < n, V k + cost k ≤ V (k+1))
    (hloss : ∑ k ∈ Finset.range n, loss k ≤ lossBound)
    (hV : V n = PlanarFalconer.potential A u w Q)
    (hQ : 0 < Q) (hwidth : u + Q ≤ w) (huf : u ≤ start n) (hfw : start n ≤ w)
    (hd : 0 ≤ d) (hN : 0 < N)
    (hlip : ∀ i, u ≤ i → i ≤ w →
      |A i - A (start n)| ≤ d * |(i : ℝ) - start n| / N) :
    (∑ k ∈ Finset.range n,
      (-2 * (A (start (k+1)) - A (start k)) + cost k + loss k)) + terminal ≤
      2 * A (start 0) - V 0 + 2 * d * Q / N + lossBound + terminal := by
  have hfinal : V n ≤ 2 * A (start n) + 2 * d * Q / N := by
    rw [hV]
    exact last_potential_bound A hQ hwidth huf hfw hd hN hlip
  exact PlanarFalconer.branch_exponent_bound A start V cost loss n _ terminal
    lossBound hpay hfinal hloss

end Falconer

end OAI
