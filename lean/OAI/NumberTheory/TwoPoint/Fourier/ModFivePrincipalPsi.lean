import OAI.NumberTheory.TwoPoint.Fourier.ModFiveUnsmoothing
import StrongPNT.Erdos970.PNT5_Strong

namespace OAI

/-! The principal character only removes powers of five.  For the required
error bound it is enough to charge the prime 5 once, and all remaining
terms to the already proved elementary prime-power error. -/

namespace TwoPointCorrelations

open Complex ArithmeticFunction Finset
open scoped BigOperators Classical

local instance : Fact (1 < (5 : ℕ)) := ⟨by decide⟩

lemma modFive_principal_term_bound (n : ℕ) :
    ‖modFiveMangoldtTwist 1 n - (vonMangoldt n : ℂ)‖ ≤
      (if n = 5 then Real.log 5 else 0) +
        (vonMangoldt n - if n.Prime then Real.log n else 0) := by
  by_cases hp : n.Prime
  · by_cases hn : n = 5
    · subst n
      have hz : (1 : DirichletCharacter ℂ 5) (5 : ZMod 5) = 0 := by
        rw [show (5 : ZMod 5) = 0 by decide, MulChar.map_zero]
      rw [modFiveMangoldtTwist]
      simp only [Nat.cast_ofNat]
      rw [hz, zero_mul, zero_sub, norm_neg, vonMangoldt_apply_prime hp]
      simp only [hp, ↓reduceIte, Nat.cast_ofNat, sub_self, add_zero]
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 5))]
    · have hcop : n.Coprime 5 := hp.coprime_iff_not_dvd.mpr (by
        intro hd
        exact hn ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp hd))
      have hu : IsUnit (n : ZMod 5) := (ZMod.isUnit_iff_coprime n 5).mpr hcop
      have hone : (1 : DirichletCharacter ℂ 5) (n : ZMod 5) = 1 := MulChar.one_apply hu
      simp [modFiveMangoldtTwist, hone, hp, hn, vonMangoldt_apply_prime hp]
  · have hn : n ≠ 5 := by intro he; subst n; exact hp (by decide)
    by_cases hu : IsUnit (n : ZMod 5)
    · have hone : (1 : DirichletCharacter ℂ 5) (n : ZMod 5) = 1 := MulChar.one_apply hu
      simp [modFiveMangoldtTwist, hone, hp, hn, vonMangoldt_nonneg]
    · have hzero : (1 : DirichletCharacter ℂ 5) (n : ZMod 5) = 0 := MulChar.map_nonunit _ hu
      simp [modFiveMangoldtTwist, hzero, hp, hn, abs_of_nonneg vonMangoldt_nonneg]

lemma modFive_principal_psi_error {x : ℝ} (hx : 1 ≤ x) :
    ‖modFiveTwistedPsi 1 x - (Chebyshev.psi x : ℂ)‖ ≤
      Real.log 5 + 2 * Real.sqrt x * Real.log x := by
  have hid : modFiveTwistedPsi 1 x - (Chebyshev.psi x : ℂ) =
      ∑ n ∈ Icc 0 ⌊x⌋₊, (modFiveMangoldtTwist 1 n - (vonMangoldt n : ℂ)) := by
    rw [modFiveTwistedPsi_eq, Chebyshev.psi_eq_sum_Icc, Complex.ofReal_sum,
      sum_sub_distrib]
  have hfive : (∑ n ∈ Icc 0 ⌊x⌋₊, if n = 5 then Real.log 5 else 0) ≤ Real.log 5 := by
    by_cases h5 : 5 ∈ Icc 0 ⌊x⌋₊
    · simp [h5]
    · simp [h5, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 5)]
  have hrem : (∑ n ∈ Icc 0 ⌊x⌋₊,
      (vonMangoldt n - if n.Prime then Real.log n else 0)) =
      Chebyshev.psi x - Chebyshev.theta x := by
    rw [sum_sub_distrib, Chebyshev.psi_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc, sum_filter]
  rw [hid]
  calc
    _ ≤ ∑ n ∈ Icc 0 ⌊x⌋₊, ‖modFiveMangoldtTwist 1 n - (vonMangoldt n : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Icc 0 ⌊x⌋₊,
        ((if n = 5 then Real.log 5 else 0) +
          (vonMangoldt n - if n.Prime then Real.log n else 0)) :=
      sum_le_sum fun n _ => modFive_principal_term_bound n
    _ = (∑ n ∈ Icc 0 ⌊x⌋₊, if n = 5 then Real.log 5 else 0) +
        (Chebyshev.psi x - Chebyshev.theta x) := by rw [sum_add_distrib, hrem]
    _ ≤ _ := add_le_add hfive (Chebyshev.psi_sub_theta_le hx)

lemma modFive_chebyshevPsi_eq {x : ℝ} (hx : 0 ≤ x) :
    Erdos970.ChebyshevPsi x = Chebyshev.psi x := by
  rw [Erdos970.ChebyshevPsi, Nat.floor_add_one hx, Nat.range_succ_eq_Icc_zero,
    Chebyshev.psi_eq_sum_Icc]

end TwoPointCorrelations

end OAI
