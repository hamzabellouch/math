import OAI.NumberTheory.Ostmann.Construction.RepeatFactorBounds

namespace OAI

/-! # Exponential size of the actual repeated-prime error -/

namespace Ostmann

open Filter
open scoped BigOperators FourierTransform SchwartzMap Classical

theorem eventual_wordRepeatFactor_bound (c : ℕ) (a b z A C : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hz : 0 < z) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (ψ : 𝓢(ℝ, ℂ)) :
    ∀ᶠ m : ℕ in atTop, ∀ (L J D : ℝ), 0 < L →
      (m : ℝ) ≤ z * L → z * L ≤ 2 * m →
      ∀ (P B T : Finset ℕ) (R : Fin c → Finset ℕ),
      a * L ≤ ∑ p ∈ B, (p : ℝ)⁻¹ → b ≤ ∑ p ∈ T, (p : ℝ)⁻¹ →
      (∀ i, Real.exp (-J) ≤ ∑ p ∈ R i, (p : ℝ)⁻¹) → J ≤ A * L →
      (∑ p : P, (p : ℝ)⁻¹) ≤ C * L →
      wordRepeatFactor P (Fin.append (fun _ : Fin m => B) (fun _ : Fin 1 => T)) R ψ D ≤
        Real.exp ((2 * Real.log (3 * z / a) + 2 + (4 * c * A + 2 * C) / z) * m - D / 2) := by
  have hcst := (Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop
    (‖𝓕 ψ 0‖ * b⁻¹ ^ 2)
  filter_upwards [eventual_repeat_multiplicity_cost (2 + 2 * c) a z ha hz,
    eventually_ge_atTop (2 + 2 * c), hcst] with m hm hmc hconst L J D hL hmL hLm P B T R hB hT hR hJ hP
  change ‖𝓕 ψ 0‖ * b⁻¹ ^ 2 ≤ Real.exp (m : ℝ) at hconst
  have hnorm := bulk_top_normalizers_le (m := m) B T R L a b J hL ha hb hB hT hR
  have hmult := hm L hL hmL hmc
  have hn : (m + 1 + c) + (m + 1 + c) = 2 * m + (2 + 2 * c) := by omega
  have hmass : 2 * c * J + (∑ p : P, (p : ℝ)⁻¹) ≤ ((4 * c * A + 2 * C) / z) * m := by
    have h₁ := mul_le_mul_of_nonneg_left hJ (show 0 ≤ (2 : ℝ) * c by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hLm (show 0 ≤ 2 * c * A + C by positivity)
    have hz' : (2 * c * A + C) * L ≤ ((4 * c * A + 2 * C) * m) / z := by
      apply (le_div_iff₀ hz).mpr
      nlinarith
    rw [div_mul_eq_mul_div]
    linarith
  unfold wordRepeatFactor
  have hpow : (((m + 1 + c) + (m + 1 + c) : ℕ) : ℝ) ^ ((m + 1 + c) + (m + 1 + c)) =
      ((2 * m + (2 + 2 * c) : ℕ) : ℝ) ^ (2 * m + (2 + 2 * c)) := by rw [hn]
  rw [hpow]
  calc
    _ ≤ ‖𝓕 ψ 0‖ * ((a * L)⁻¹ ^ (2 * m) * b⁻¹ ^ 2 * Real.exp (2 * c * J)) *
        ((2 * m + (2 + 2 * c) : ℕ) : ℝ) ^ (2 * m + (2 + 2 * c)) *
        Real.exp ((∑ p : P, (p : ℝ)⁻¹) - D / 2) := by
      gcongr
    _ = (‖𝓕 ψ 0‖ * b⁻¹ ^ 2) *
        ((a * L)⁻¹ ^ (2 * m) * ((2 * m + (2 + 2 * c) : ℕ) : ℝ) ^ (2 * m + (2 + 2 * c))) *
        Real.exp (2 * c * J + (∑ p : P, (p : ℝ)⁻¹) - D / 2) := by
      simp only [Real.exp_sub, Real.exp_add]
      ring
    _ ≤ Real.exp (m : ℝ) * Real.exp ((2 * Real.log (3 * z / a) + 1) * m) *
        Real.exp (((4 * c * A + 2 * C) / z) * m - D / 2) := by
      gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Ostmann

end OAI
