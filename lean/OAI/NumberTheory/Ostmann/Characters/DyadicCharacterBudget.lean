import OAI.NumberTheory.Ostmann.Construction.OneSidedDecayBudget
import OAI.NumberTheory.Ostmann.Construction.DyadicSupportedHistory

namespace OAI

/-! # Explicit scale decay for the dyadic supported-history estimate -/

namespace Ostmann

open Filter

theorem dyadic_character_numeric_bound (N CP CQ M R B a b q K α β γ c L : ℝ)
    (hN : 0 ≤ N) (hCP : 0 ≤ CP) (hCQ : 0 ≤ CQ) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hb : Real.exp (c * Real.exp (α * L)) ≤ b)
    (ha : Real.exp (Real.exp (β * L)) ≤ a)
    (hq : 0 ≤ q) (hqupper : q ≤ Real.exp (Real.exp (γ * L)))
    (hcost₁ : 2 * N * CP * CQ * B ^ 2 ≤ K)
    (hcost₂ : 2 * N * CP * M * R * B ^ 2 ≤ K) :
    N * CP * (CQ * b⁻¹ * (2 * B ^ 2) + M * (R * (2 * a⁻¹ * B ^ 2)) * q ^ 2) ≤
      K * (Real.exp (-c * Real.exp (α * L)) +
        Real.exp (2 * Real.exp (γ * L) - Real.exp (β * L))) := by
  have hb' : b⁻¹ ≤ Real.exp (-c * Real.exp (α * L)) := by
    simpa only [← Real.exp_neg, neg_mul] using inv_anti₀ (Real.exp_pos _) hb
  have ha' : a⁻¹ * q ^ 2 ≤
      Real.exp (2 * Real.exp (γ * L) - Real.exp (β * L)) := by
    calc
      _ ≤ (Real.exp (Real.exp (β * L)))⁻¹ * (Real.exp (Real.exp (γ * L))) ^ 2 :=
        mul_le_mul (inv_anti₀ (Real.exp_pos _) ha)
          (pow_le_pow_left₀ hq hqupper 2) (sq_nonneg q) (by positivity)
      _ = _ := by rw [← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  have h₁ := mul_le_mul_of_nonneg_left hb' (by positivity : 0 ≤ 2 * N * CP * CQ * B ^ 2)
  have h₂ := mul_le_mul_of_nonneg_left ha' (by positivity : 0 ≤ 2 * N * CP * M * R * B ^ 2)
  calc
    _ = (2 * N * CP * CQ * B ^ 2) * b⁻¹ +
        (2 * N * CP * M * R * B ^ 2) * (a⁻¹ * q ^ 2) := by ring
    _ ≤ (2 * N * CP * CQ * B ^ 2) * Real.exp (-c * Real.exp (α * L)) +
        (2 * N * CP * M * R * B ^ 2) *
          Real.exp (2 * Real.exp (γ * L) - Real.exp (β * L)) := add_le_add h₁ h₂
    _ ≤ K * Real.exp (-c * Real.exp (α * L)) +
        K * Real.exp (2 * Real.exp (γ * L) - Real.exp (β * L)) :=
      add_le_add (mul_le_mul_of_nonneg_right hcost₁ (Real.exp_pos _).le)
        (mul_le_mul_of_nonneg_right hcost₂ (Real.exp_pos _).le)
    _ = _ := by ring

/-- All six concrete loss factors may be charged to one polynomial exponent.
The short-prime atom and the long/short gap remain outside that exponent. -/
theorem dyadic_character_cost (N CP CQ M R B P : ℝ)
    (_hN : 0 ≤ N) (hCP : 0 ≤ CP) (hCQ : 0 ≤ CQ) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hB : 0 ≤ B) (hP : 0 ≤ P)
    (bN : N ≤ Real.exp P) (bCP : CP ≤ Real.exp P) (bCQ : CQ ≤ Real.exp P)
    (bM : M ≤ Real.exp P) (bR : R ≤ Real.exp P) (bB : B ≤ Real.exp P) :
    2 * N * CP * CQ * B ^ 2 ≤ Real.exp (Real.log 2 + 6 * P) ∧
      2 * N * CP * M * R * B ^ 2 ≤ Real.exp (Real.log 2 + 6 * P) := by
  have he : 1 ≤ Real.exp P := Real.one_le_exp hP
  have hpow : (Real.exp P) ^ 5 ≤ (Real.exp P) ^ 6 := pow_le_pow_right₀ he (by omega)
  have hexact : 2 * (Real.exp P) ^ 6 = Real.exp (Real.log 2 + 6 * P) := by
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_nat_mul]
    norm_num
  constructor
  · calc
      _ ≤ 2 * Real.exp P * Real.exp P * Real.exp P * (Real.exp P) ^ 2 := by gcongr
      _ = 2 * (Real.exp P) ^ 5 := by ring
      _ ≤ 2 * (Real.exp P) ^ 6 := by gcongr
      _ = _ := hexact
  · calc
      _ ≤ 2 * Real.exp P * Real.exp P * Real.exp P * Real.exp P * (Real.exp P) ^ 2 := by gcongr
      _ = _ := by rw [← hexact]; ring

/-- The finite dyadic estimate implies the required double-exponential
smallness uniformly over every allowed collection of numerical parameters. -/
theorem eventual_dyadic_character_decay (C z α β γ c : ℝ) (d : ℕ)
    (hC : 0 ≤ C) (hz : 0 ≤ z) (hα : 0 < α) (hαβ : α < β)
    (hγβ : γ < β) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, ∀ (m N CP CQ M R B a b q : ℝ) (w : ℂ),
      0 ≤ m → m ≤ z * L → 0 ≤ N → 0 ≤ CP → 0 ≤ CQ → 0 ≤ M → 0 ≤ R →
      Real.exp (c * Real.exp (α * L)) ≤ b → Real.exp (Real.exp (β * L)) ≤ a →
      0 ≤ q → q ≤ Real.exp (Real.exp (γ * L)) →
      2 * N * CP * CQ * B ^ 2 ≤ Real.exp (C * (1 + m) ^ d) →
      2 * N * CP * M * R * B ^ 2 ≤ Real.exp (C * (1 + m) ^ d) →
      ‖w‖ ^ 2 ≤ N * CP *
        (CQ * b⁻¹ * (2 * B ^ 2) + M * (R * (2 * a⁻¹ * B ^ 2)) * q ^ 2) →
      ‖w‖ ≤ Real.exp (-(c / 4) * Real.exp (α * L)) := by
  filter_upwards [eventual_one_sided_amplitude_budget C z α β γ c d hC hz hα hαβ hγβ hc]
    with L hL m N CP CQ M R B a b q w hm hmL hN hCP hCQ hM hR hb ha hq hqupper h₁ h₂ hw
  apply hL m w hm hmL
  exact hw.trans (dyadic_character_numeric_bound N CP CQ M R B a b q _ α β γ c L
    hN hCP hCQ hM hR hb ha hq hqupper h₁ h₂)

end Ostmann

end OAI
