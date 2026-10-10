import OAI.NumberTheory.Ostmann.Supply.FavorableMassAlternative
import OAI.NumberTheory.Ostmann.Supply.SieveBudgetParameters

namespace OAI

/-! # The large sparse set forced by failure of favorable-prime mass -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

theorem logLog_sparse_mass_lower {C : ℝ} (hM : MertensHarmonicEstimate C)
    (L : ℝ) (hL : 40 ≤ L) (S T : ℕ → Finset ℕ)
    (μ ν : ℕ → ℕ → ℝ) (γ : ℕ → ℝ) (δ D : ℝ)
    (hS : ∀ p ∈ logLogPrimeBand L, (S p).Nonempty)
    (hT : ∀ p ∈ logLogPrimeBand L, (T p).Nonempty)
    (hcard : ∀ p ∈ logLogPrimeBand L, (S p).card + (T p).card = p)
    (hbudget : (∑ p ∈ logLogPrimeBand L, Real.log (p : ℝ) *
      collisionDefect p (S p) (T p) (μ p) (ν p)) ≤ D)
    (hfail : (∑ p ∈ favorableTransformPrimes (logLogPrimeBand L) S γ δ, (p : ℝ)⁻¹) ≤
      (3 / 20 : ℝ) * L) :
    (7 / 10 : ℝ) * L - Real.log 2 - 2 * C - 4 * D / Real.exp ((1 / 20 : ℝ) * L) ≤
      ∑ p ∈ sparseTransformPrimes (logLogPrimeBand L) S γ δ, (p : ℝ)⁻¹ := by
  have hh := sparse_transform_mass_lower (logLogPrimeBand L) S T μ ν γ δ
    (Real.exp ((1 / 20 : ℝ) * L)) D (Real.exp_pos _)
    (fun p hp => (logLogPrimeBand_mem hp).1)
    (fun p hp => (logLogPrimeBand_mem hp).2.1.le) hS hT hcard hbudget
  have hm := logLogPrimeBand_harmonic_lower hM L hL
  linarith

theorem eventual_sparse_mass_error (C d e : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ D : ℝ, D ≤ d * L + e →
      (69 / 100 : ℝ) * L ≤
        (7 / 10 : ℝ) * L - Real.log 2 - 2 * C - 4 * D / Real.exp ((1 / 20 : ℝ) * L) := by
  have hlin := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1 / 20 : ℝ) (by norm_num)
  have hcon := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (1 / 20 : ℝ) (by norm_num)
  simp only [Real.rpow_one] at hlin
  simp only [Real.rpow_zero, one_mul] at hcon
  have hz : Tendsto (fun L : ℝ => 4 * (d * L + e) / Real.exp ((1 / 20 : ℝ) * L))
      atTop (nhds 0) := by
    have hh := (hlin.const_mul (4 * d)).add (hcon.const_mul (4 * e))
    simp only [mul_zero, add_zero] at hh
    apply hh.congr
    intro L
    simp only [div_eq_mul_inv, neg_mul, Real.exp_neg]
    ring
  filter_upwards [hz.eventually_lt_const (show (0 : ℝ) < 1 by norm_num),
    eventually_ge_atTop (100 * (Real.log 2 + 2 * C + 1))] with L herr hL D hD
  have hd : 4 * D / Real.exp ((1 / 20 : ℝ) * L) ≤ 1 := by
    apply le_trans _ herr.le
    exact div_le_div_of_nonneg_right (by linarith) (Real.exp_pos _).le
  linarith

theorem sparse_band_mass_after_one_deletion (L : ℝ) (hL : 50 ≤ L)
    (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (hmass : (69 / 100 : ℝ) * L ≤ ∑ p ∈ P, (p : ℝ)⁻¹) (q : ℕ) :
    (17 / 25 : ℝ) * L ≤ ∑ p ∈ P.erase q, (p : ℝ)⁻¹ := by
  by_cases hq : q ∈ P
  · have htwo : (2 : ℝ) ≤ q := by exact_mod_cast (hP q hq).two_le
    have hi : (q : ℝ)⁻¹ ≤ 1 / 2 := by
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) htwo
    have he := Finset.sum_erase_add P (fun p => (p : ℝ)⁻¹) hq
    linarith
  · rw [Finset.erase_eq_of_notMem hq]
    linarith

end Ostmann

end OAI
