import OAI.NumberTheory.Ostmann.QuadraticCenter.HighWeightResidueMass
import OAI.NumberTheory.Ostmann.QuadraticCenter.RankinParameterBudget
import OAI.NumberTheory.Ostmann.Characters.SquarefreeCoefficientBudget

namespace OAI

/-! # Exponential decay of the actual high-weight residue mass -/

namespace Ostmann

open Filter
open scoped BigOperators

/-- The high-weight estimate at the manuscript's moment and kernel scales.
The set consists of actual squarefree integers in a dyadic residue class;
neither a reciprocal-mass estimate nor a half-kernel count is assumed. -/
theorem eventual_high_weight_residue_mass (C : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ (N L a : ℕ) (S : Finset ℕ) (u : ℝ),
      0 < L → 2 * L ^ 2 ≤ N → (2 * N : ℝ) ≤ Real.exp (C * T) →
      (∀ s ∈ S, Squarefree s) →
      (∀ s ∈ S, s ∈ Finset.Ioc N (2 * N)) →
      (∀ s ∈ S, Nat.ModEq L s a) → (∀ s ∈ S, L.Coprime s) →
      2 ≤ u → u ≤ 4 * T ^ (1 / 1000000 : ℝ) →
      (∀ s ∈ S, Real.exp (T ^ (9999999 / 10000000 : ℝ) / 200) < u ^ s.primeFactors.card) →
      (∑ s ∈ S, u ^ s.primeFactors.card) ≤
        ((N : ℝ) / L) * Real.exp (-10 * T ^ (9999999 / 10000000 : ℝ)) := by
  let B : ℝ := 1 + Real.log (max 1 (C / Real.log 2))
  have hB : 1 ≤ B := by
    dsimp [B]
    linarith [Real.log_nonneg (le_max_left (1 : ℝ) (C / Real.log 2))]
  have hbudget := rankin_parameter_budget (4 * B) (by positivity)
  filter_upwards [hbudget, eventually_ge_atTop (2 : ℝ)] with T hbudget hT N L a S u
    hL hsize hcut hS hrange hres hcop hu huU hhigh
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hu1 : 1 < u := by linarith
  let K : ℝ := T ^ (9999999 / 10000000 : ℝ)
  let b : ℕ := ⌈K / (400 * Real.log u) - 1⌉₊
  have hK : 1 ≤ K := Real.one_le_rpow hT1 (by norm_num)
  have hb (s : ℕ) (hs : s ∈ S) : b ≤ (smallHalfKernel s).primeFactors.card := by
    apply Nat.ceil_le.mpr
    have hh := high_weight_half_kernel_card s (smallHalfKernel s)
      (smallHalfKernel_spec s (hS s hs)).2.2.2 u K (1 / 200) hu1 (by
        simpa only [one_div_mul_eq_div] using hhigh s hs)
    convert hh using 1
    ring
  have hP (s : ℕ) (hs : s ∈ S) :
      (smallHalfKernel s).primeFactors ⊆ Nat.primesLE (2 * N) := by
    intro p hp
    obtain ⟨hpp, hpr, _⟩ := Nat.mem_primeFactors.mp hp
    have hs0 := Nat.pos_of_ne_zero (hS s hs).ne_zero
    have hps : p ∣ s := dvd_trans hpr (smallHalfKernel_spec s (hS s hs)).2.1
    exact Nat.mem_primesLE.mpr
      ⟨(Nat.le_of_dvd hs0 hps).trans (Finset.mem_Ioc.mp (hrange s hs)).2, hpp⟩
  have hprime := prime_reciprocal_exponential_cutoff C T hT1 (2 * N) (by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hcut)
  have hprime' : (∑ p ∈ Nat.primesLE (2 * N), (p : ℝ)⁻¹) ≤
      (4 * B) * (1 + Real.log T) := by
    apply hprime.trans
    change 4 * (B + Real.log T) ≤ _
    have hh := mul_le_mul_of_nonneg_right hB (Real.log_nonneg hT1)
    nlinarith
  have hE : Real.log u + Real.log T / 4 +
      u ^ 2 * T ^ (1 / 4 : ℝ) * (∑ p ∈ Nat.primesLE (2 * N), (p : ℝ)⁻¹) ≤ K := by
    apply le_trans _ (hbudget u hu huU).2
    have hh := mul_le_mul_of_nonneg_left hprime'
      (show 0 ≤ u ^ 2 * T ^ (1 / 4 : ℝ) by positivity)
    nlinarith only [hh]
  have hdecay := rankin_exponential_bound T u K
    (u ^ 2 * T ^ (1 / 4 : ℝ) * ∑ p ∈ Nat.primesLE (2 * N), (p : ℝ)⁻¹)
    b (by linarith) hu1 (by positivity) (hbudget u hu huU).1 (Nat.le_ceil _) hE
  have hmass := high_weight_residue_mass S (Nat.primesLE (2 * N)) N L a b
    hL hsize hS hrange hres hcop hP hb u (T ^ (1 / 4 : ℝ)) (by linarith)
    (Real.one_le_rpow hT1 (by norm_num))
  have hNL : 0 ≤ (N : ℝ) / L := by positivity
  have htwo : 2 * Real.exp (-20 * K) ≤ Real.exp (-10 * K) := by
    calc
      _ = Real.exp (Real.log 2 - 20 * K) := by
        have he : Real.log 2 - 20 * K = Real.log 2 + (-20 * K) := by ring
        rw [he, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ ≤ _ := Real.exp_le_exp.mpr (by
        have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith)
  calc
    _ ≤ _ := hmass
    _ = ((N : ℝ) / L) * (2 * (u * ((T ^ (1 / 4 : ℝ)) ^ b)⁻¹ *
        Real.exp (u ^ 2 * T ^ (1 / 4 : ℝ) * ∑ p ∈ Nat.primesLE (2 * N), (p : ℝ)⁻¹))) := by ring
    _ ≤ ((N : ℝ) / L) * (2 * Real.exp (-20 * K)) := by gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_left htwo hNL

end Ostmann

end OAI
