import OAI.NumberTheory.Ostmann.Construction.GoodPrimeLogCells
import OAI.NumberTheory.Ostmann.Construction.RetainedPrimeNormalization

namespace OAI

/-! # The chosen small cells meet the original prior's exponential budget -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem eventual_cell_harmonic_floor :
    ∀ᶠ L : ℝ in atTop, ∀ h : ℕ, (h : ℝ) ≤ Real.exp (L / 2) →
      Real.exp (-L) ≤ 1 / (4 * ((h : ℝ) + 1)) := by
  filter_upwards [eventually_ge_atTop (max 0 (2 * Real.log 8))] with L hL h hh
  have hL0 : 0 ≤ L := (le_max_left _ _).trans hL
  have he1 : 1 ≤ Real.exp (L / 2) := Real.one_le_exp (by positivity)
  have he8 : 8 ≤ Real.exp (L / 2) := by
    have hh := Real.exp_le_exp.mpr (show Real.log 8 ≤ L / 2 by
      have := (le_max_right (0 : ℝ) (2 * Real.log 8)).trans hL
      linarith)
    rwa [Real.exp_log (by norm_num : (0 : ℝ) < 8)] at hh
  have hden : 4 * ((h : ℝ) + 1) ≤ Real.exp L := by
    have he : Real.exp (L / 2) * Real.exp (L / 2) = Real.exp L := by
      rw [← Real.exp_add]; congr 1; ring
    have hm := mul_le_mul_of_nonneg_right he8 (Real.exp_nonneg (L / 2))
    nlinarith only [hh, he1, hm, he]
  have hi := one_div_le_one_div_of_le
    (by positivity : (0 : ℝ) < 4 * ((h : ℝ) + 1)) hden
  simpa only [one_div, ← Real.exp_neg] using hi

theorem selected_cell_after_finite_deletion :
    ∀ᶠ L : ℝ in atTop, ∀ (h : ℕ) (Q D : Finset ℕ),
      Real.exp ((39 / 10000 : ℝ) * L) ≤ h → (h : ℝ) ≤ Real.exp (L / 2) →
      Q ⊆ primeLogCellSet 1 0 h ((h : ℝ) + 1) →
      1 / (4 * ((h : ℝ) + 1)) ≤ ∑ p ∈ Q, (p : ℝ)⁻¹ →
      (D.card : ℝ) ≤ Real.exp L →
      Real.exp (-(2 * L)) ≤ ∑ p ∈ Q \ D, (p : ℝ)⁻¹ ∧
      0 < (∑ p ∈ Q \ D, (p : ℝ)⁻¹) ∧
      (∑ p ∈ Q \ D, (p : ℝ)⁻¹)⁻¹ ≤ Real.exp (2 * L) := by
  filter_upwards [eventual_cell_harmonic_floor,
    retained_prime_normalizer_rate 1 (by norm_num)] with L hfloor hnormal
  intro h Q D hhlo hhhi hQ hmass hD
  have hn := hnormal Q D h (by simpa using (hfloor h hhhi).trans hmass)
    (by simpa only [one_mul] using hD) hhlo (fun p hp => by
      obtain ⟨hpprime, _, hlog, _⟩ := mem_primeLogCellSet_iff.mp (hQ hp)
      exact ((Real.lt_log_iff_exp_lt (by exact_mod_cast hpprime.pos)).mp hlog).le)
  have hinv : (∑ p ∈ Q \ D, (p : ℝ)⁻¹)⁻¹ ≤ Real.exp (2 * L) := by
    simpa only [show (1 + 1 : ℝ) = 2 by norm_num] using hn.2
  have hlo := inv_anti₀ (inv_pos.mpr hn.1) hinv
  refine ⟨?_, hn.1, hinv⟩
  simpa only [inv_inv, ← Real.exp_neg] using hlo

end Ostmann

end OAI
