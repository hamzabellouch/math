import Mathlib.Analysis.SpecialFunctions.Pow.Real
import OAI.NumberTheory.Ostmann.QuadraticSieveRecursionDescent

namespace OAI

namespace Ostmann.QuadraticSieve

noncomputable def smoothingDescentScale (N R : ℕ) : ℕ := ⌈(N : ℝ)^(1/(R : ℝ))⌉₊

theorem smoothingDescentScale_bounds {N R : ℕ} (hN : 0 < N) (hR : 0 < R) :
    1 ≤ smoothingDescentScale N R ∧
      (N : ℝ) ≤ (smoothingDescentScale N R : ℝ)^R ∧
      (smoothingDescentScale N R : ℝ) ≤ 2*(N : ℝ)^(1/(R : ℝ)) ∧
      (smoothingDescentScale N R : ℝ)^5 ≤ 32*(N : ℝ)^(5/(R : ℝ)) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hRp : (0 : ℝ) < R := by exact_mod_cast hR
  have hroot : 1 ≤ (N : ℝ)^(1/(R : ℝ)) := Real.one_le_rpow hN1 (by positivity)
  have hlo : (N : ℝ)^(1/(R : ℝ)) ≤ (smoothingDescentScale N R : ℝ) := Nat.le_ceil _
  have hD1 : 1 ≤ smoothingDescentScale N R := by exact_mod_cast hroot.trans hlo
  have hhi : (smoothingDescentScale N R : ℝ) ≤ 2*(N : ℝ)^(1/(R : ℝ)) := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ (N : ℝ)^(1/(R : ℝ)) by positivity)
    change (smoothingDescentScale N R : ℝ) < (N : ℝ)^(1/(R : ℝ))+1 at hh
    linarith
  have hpow : ((N : ℝ)^(1/(R : ℝ)))^R = (N : ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hNp.le]
    have he : 1/(R : ℝ)*(R : ℝ) = 1 := by field_simp
    rw [he,Real.rpow_one]
  have hpow5 : ((N : ℝ)^(1/(R : ℝ)))^5 = (N : ℝ)^(5/(R : ℝ)) := by
    rw [← Real.rpow_ofNat,← Real.rpow_mul hNp.le]
    congr 1
    ring
  refine ⟨hD1,?_,hhi,?_⟩
  · rw [← hpow]
    exact pow_le_pow_left₀ (by positivity) hlo R
  · calc
      _ ≤ (2*(N : ℝ)^(1/(R : ℝ)))^5 := pow_le_pow_left₀ (Nat.cast_nonneg _) hhi 5
      _ = 32*(N : ℝ)^(5/(R : ℝ)) := by rw [mul_pow,hpow5]; norm_num

theorem exists_smoothing_descent_scale (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℕ, 0 < R ∧ ∀ N : ℕ, 0 < N →
      1 ≤ smoothingDescentScale N R ∧
      (N : ℝ) ≤ (smoothingDescentScale N R : ℝ)^R ∧
      (smoothingDescentScale N R : ℝ)^5 ≤ 32*(N : ℝ)^ε := by
  obtain ⟨R,hR⟩ := exists_nat_gt (5/ε)
  have hRp : (0 : ℝ) < R := (by positivity : 0 < 5/ε).trans hR
  have hRn : 0 < R := by exact_mod_cast hRp
  have hratio : 5/(R : ℝ) ≤ ε := by
    apply (div_le_iff₀ hRp).mpr
    have hh := (div_lt_iff₀ hε).mp hR
    nlinarith
  refine ⟨R,hRn,?_⟩
  intro N hN
  obtain ⟨hD,hsize,hupper,hpow⟩ := smoothingDescentScale_bounds hN hRn
  refine ⟨hD,hsize,hpow.trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hratio) (by norm_num)

end Ostmann.QuadraticSieve

end OAI
