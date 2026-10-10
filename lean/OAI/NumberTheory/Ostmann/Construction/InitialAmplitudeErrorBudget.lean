import OAI.NumberTheory.Ostmann.Construction.InitialRepeatedErrorRate
import OAI.NumberTheory.Ostmann.Construction.BalancedEndpointRate

namespace OAI

/-! # The actual initial statistic pays for the repeated-prime error -/
namespace Ostmann
open Filter

theorem eventual_initial_amplitude_error_budget (r : ℕ)
    (z K A B Bs a c δ A₀ : ℝ)
    (hz : 1 ≤ z) (ha : 0 < a) (hc : 0 < c) (hδ : 0 < δ)
    (hBs : 2 * (A + B + 2 * Real.log 4 + (2 * A₀ + 2 * Real.log 2 + 4) + 3) ≤ Bs) :
    ∀ᶠ m : ℕ in atTop, ∀ (L Y X E C H Δ : ℝ) (n : ℕ),
      0 < L → L ≤ m → (m : ℝ) ≤ z * L →
      0 < Y → Y ≤ Real.exp L → 0 ≤ X → n ≤ m + r →
      a * Real.sqrt X / Y ^ 3 ≤ E →
      0 ≤ C → C * L ^ (2 * m) ≤ Real.exp (A * m) → H ≤ B * m →
      (Bs + 8 * Real.log z) * m ≤ Δ →
      Real.sqrt X * (Real.exp (-(2 * A₀ + 2 * Real.log 2 + 5) * m) +
        K * C * ((2 * (m + (r + 1)) : ℕ) : ℝ) ^ (2 * (m + (r + 1))) *
          Real.exp (H - Δ / 2)) ≤
        E * (c * (Real.exp (-A₀ * m) * (1 / 2 : ℝ) ^ n * δ) ^ 2) := by
  let Q := 2 * A₀ + 2 * Real.log 2 + 4
  have herr := eventual_initial_repeated_error (r + 1) z K A B Bs Q hz hBs
  have hend := eventual_balanced_endpoint_rate r a c δ A₀ ha hc hδ
  have htwo : ∀ᶠ m : ℕ in atTop, Real.log 2 ≤ (m : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [herr, hend, htwo] with m herr hend htwo
    L Y X E C H Δ n hL hLm hmL hY hYL hX hn hE hC hnorm hH hgap
  have he := herr L C H Δ hL hmL hC hnorm hH hgap
  have hs := hend L Y X E n hLm hY hYL hX hn hE
  have hfactor : 2 * Real.exp (-(m : ℝ)) ≤ 1 := by
    calc
      _ ≤ 2 * Real.exp (-Real.log 2) := by gcongr
      _ = 1 := by rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num
  have hsum : Real.exp (-(Q + 1) * m) + Real.exp (-(Q + 1) * m) ≤ Real.exp (-Q * m) := by
    calc
      _ = Real.exp (-Q * m) * (2 * Real.exp (-(m : ℝ))) := by
        rw [show -(Q + 1) * (m : ℝ) = -Q * m + -(m : ℝ) by ring, Real.exp_add]
        ring
      _ ≤ _ := by simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hfactor (Real.exp_nonneg (-Q * m))
  apply le_trans _ hs
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg X)
  have ht := (add_le_add_left he (Real.exp (-(Q + 1) * m))).trans hsum
  rw [show Q + 1 = 2 * A₀ + 2 * Real.log 2 + 5 by dsimp [Q]; ring] at ht
  dsimp only [Q] at ht
  linarith only [ht]

end Ostmann

end OAI
