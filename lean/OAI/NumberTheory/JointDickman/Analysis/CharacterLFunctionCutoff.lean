import OAI.NumberTheory.JointDickman.Analysis.DirichletGrowth
import OAI.NumberTheory.JointDickman.Analysis.DyadicDirichletSum

namespace OAI

/-! # A bounded remainder after truncating a nonprincipal Dirichlet L-series -/
namespace JointDickman
open Complex Finset LargePrimeGaps

lemma sum_nat_Icc_int_cast {E : Type*} [AddCommMonoid E] (f : ℤ → E) (a b : ℕ) :
    (∑ n ∈ Icc a b, f (n:ℤ)) = ∑ n ∈ Icc (a:ℤ) (b:ℤ), f n := by
  apply sum_bij (fun (n : ℕ) _ => (n:ℤ))
  · intro n hn
    exact mem_Icc.mpr ⟨by exact_mod_cast (mem_Icc.mp hn).1,
      by exact_mod_cast (mem_Icc.mp hn).2⟩
  · intro n _ m _ h
    exact_mod_cast h
  · intro m hm
    have hm0 : 0 ≤ m := (Nat.cast_nonneg a).trans (mem_Icc.mp hm).1
    refine ⟨m.toNat, mem_Icc.mpr ⟨?_,?_⟩, Int.toNat_of_nonneg hm0⟩
    · exact_mod_cast (show (a:ℤ) ≤ (m.toNat:ℤ) by simpa [Int.toNat_of_nonneg hm0] using (mem_Icc.mp hm).1)
    · exact_mod_cast (show (m.toNat:ℤ) ≤ (b:ℤ) by simpa [Int.toNat_of_nonneg hm0] using (mem_Icc.mp hm).2)
  · intro n hn
    rfl

lemma character_LFunction_cutoff_bound {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (s : ℂ) (hs : 1 ≤ s.re)
    (hs2 : s.re ≤ 2) (N : ℕ) (hN : 1 ≤ N) (ht : |s.im| ≤ N) :
    ‖χ.LFunction s - ∑ n ∈ Icc 1 N, χ (n:ZMod q)*(n:ℂ)^(-s)‖ ≤ 4*((q:ℝ)+1) := by
  have hs0 : 0 < s.re := by linarith
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0:ℝ) < N := by linarith
  let A := seriesDiscrepancy (positiveCoefficients (fun n => χ (n:ZMod q))) 0
  have he := regularSeries_cutoff (positiveCoefficients_zero (fun n => χ (n:ZMod q)))
    (D := (q:ℝ)+1) (by positivity) (fun t _ => discrepancy_character_bound hχ t) hN hs0
  rw [regularSeries_character_eq hχ hs0] at he
  simp only [zero_mul, sub_zero] at he
  have hp : (∑ n ∈ Icc 1 N, positiveCoefficients (fun n => χ (n:ZMod q)) n*(n:ℂ)^(-s)) =
      ∑ n ∈ Icc 1 N, χ (n:ZMod q)*(n:ℂ)^(-s) := by
    apply sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
    simp [positiveCoefficients, hn0]
  rw [hp] at he
  have htbound := discrepancyTail_norm_le hN0 (by positivity : (0:ℝ) ≤ q+1)
    (measurable_seriesDiscrepancy _ (0:ℂ))
    (fun t (_ : (N:ℝ) < t) => discrepancy_character_bound hχ t) hs0
  have hpow : (N:ℝ)^(-s.re) ≤ (N:ℝ)⁻¹ := by
    simpa only [Real.rpow_neg_one] using Real.rpow_le_rpow_of_exponent_le hNR (show -s.re ≤ -1 by linarith)
  have hnorm : ‖s‖ ≤ 2+(N:ℝ) := by
    have hh := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos hs0] at hh
    linarith
  have htail : ‖discrepancyTail A N s‖ ≤ ((q:ℝ)+1)*(N:ℝ)⁻¹ := by
    exact htbound.trans (by
      calc
        _ ≤ ((q:ℝ)+1)*(N:ℝ)^(-s.re) := div_le_self (by positivity) hs
        _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity))
  have hc : ‖A N * (N:ℂ)^(-s)‖ ≤ ((q:ℝ)+1)*(N:ℝ)⁻¹ := by
    rw [norm_mul, show (N:ℂ) = ((N:ℝ):ℂ) by simp,
      norm_cpow_eq_rpow_re_of_pos hN0, neg_re]
    exact mul_le_mul (discrepancy_character_bound hχ N) hpow (by positivity) (by positivity)
  have herr : χ.LFunction s - ∑ n ∈ Icc 1 N, χ (n:ZMod q)*(n:ℂ)^(-s) =
      -(A N*(N:ℂ)^(-s))+s*discrepancyTail A N s := by
    dsimp [A]
    rw [he]
    abel
  rw [herr]
  calc
    _ ≤ ‖A N*(N:ℂ)^(-s)‖ + ‖s‖*‖discrepancyTail A N s‖ := by
      simpa only [norm_neg,norm_mul] using norm_add_le (-(A N*(N:ℂ)^(-s))) (s*discrepancyTail A N s)
    _ ≤ ((q:ℝ)+1)*(N:ℝ)⁻¹ + (2+(N:ℝ))*(((q:ℝ)+1)*(N:ℝ)⁻¹) :=
      add_le_add hc (mul_le_mul hnorm htail (norm_nonneg _) (by positivity))
    _ ≤ 4*((q:ℝ)+1) := by
      have hNi : (N:ℝ)*(N:ℝ)⁻¹ = 1 := mul_inv_cancel₀ hN0.ne'
      have hile : (N:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hNR
      nlinarith [Nat.cast_nonneg (α := ℝ) q]

lemma character_LFunction_head_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : 1 ≤ s.re) (N : ℕ) :
    ‖∑ n ∈ Icc 1 N, χ (n:ZMod q)*(n:ℂ)^(-s)‖ ≤ 1+Real.log N := by
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ‖χ (n:ZMod q)*(n:ℂ)^(-s)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Icc 1 N, (n:ℝ)⁻¹ := by
      apply sum_le_sum
      intro n hn
      have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
      rw [norm_mul, show (n:ℂ) = ((n:ℝ):ℂ) by simp,
        norm_cpow_eq_rpow_re_of_pos (by linarith), neg_re]
      exact (mul_le_of_le_one_left (by positivity) (χ.norm_le_one _)).trans
        (by simpa only [Real.rpow_neg_one] using Real.rpow_le_rpow_of_exponent_le hn1 (show -s.re ≤ -1 by linarith))
    _ = (harmonic N:ℝ) := by simp [harmonic_eq_sum_Icc]
    _ ≤ _ := harmonic_le_one_add_log N

end JointDickman

end OAI
