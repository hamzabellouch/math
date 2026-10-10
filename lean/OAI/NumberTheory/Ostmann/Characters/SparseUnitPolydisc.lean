import OAI.NumberTheory.Ostmann.Characters.SparseKernelUnitFactor
import OAI.NumberTheory.Ostmann.Characters.SparsePolydiscScalar

namespace OAI

/-! # Uniform control of the scalar unit mean on the parameter polydisc -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def sparseUnitPolynomial (p e : ℝ) (c d : ℂ) : ℂ :=
  1 + c * ((-(17 / 20) * e / (p - 1) : ℝ) : ℂ) +
    d * (((17 / 20) ^ 2 * (e - e ^ 2) / (p - 1) : ℝ) : ℂ)

theorem small_unit_ratio (p x ε : ℝ) (hp : 2 ≤ p) (hx : x ≤ ε) (hε : 0 ≤ ε) :
    x / (p - 1) ≤ 2 * ε / p := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  apply (div_le_div_iff₀ hp1 hp0).mpr
  have hh := mul_le_mul_of_nonneg_right hx hp0.le
  nlinarith [mul_nonneg hε (sub_nonneg.mpr hp)]

theorem sparseUnitPolynomial_norm_le (p e ε : ℝ) (c d : ℂ)
    (hp : 2 ≤ p) (he : 0 ≤ e) (heε : e ≤ ε) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hc : ‖c‖ ≤ 103 / 50) (hd : ‖d‖ ≤ 10609 / 10000) :
    ‖sparseUnitPolynomial p e c d‖ ≤ 1 + 6 / p := by
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have he1 : e ≤ 1 := heε.trans hε1
  have hv : 0 ≤ e - e ^ 2 := by nlinarith
  have hve : e - e ^ 2 ≤ ε := by nlinarith [sq_nonneg e]
  have hr1 := small_unit_ratio p e ε hp heε hε
  have hr2 := small_unit_ratio p (e - e ^ 2) ε hp hve hε
  have h1 : ‖((-(17 / 20) * e / (p - 1) : ℝ) : ℂ)‖ ≤ (17 / 10) * ε / p := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg he,
      abs_of_pos hp1]
    norm_num
    have hh := mul_le_mul_of_nonneg_left hr1 (by norm_num : (0 : ℝ) ≤ 17 / 20)
    convert hh using 1 <;> ring
  have h2 : ‖(((17 / 20) ^ 2 * (e - e ^ 2) / (p - 1) : ℝ) : ℂ)‖ ≤ (289 / 200) * ε / p := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hh := mul_le_mul_of_nonneg_left hr2 (by norm_num : (0 : ℝ) ≤ (17 / 20) ^ 2)
    convert hh using 1 <;> ring
  unfold sparseUnitPolynomial
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_add_le _ _) le_rfl).trans
  rw [norm_one, norm_mul, norm_mul]
  have hh := add_le_add (mul_le_mul hc h1 (norm_nonneg _) (by norm_num))
    (mul_le_mul hd h2 (norm_nonneg _) (by norm_num))
  have hfrac : ((103 / 50) * ((17 / 10) * ε / p) +
      (10609 / 10000) * ((289 / 200) * ε / p)) ≤ 6 / p := by
    apply (le_div_iff₀ hp0).mpr
    have heq : ((103 / 50) * ((17 / 10) * ε / p) +
        (10609 / 10000) * ((289 / 200) * ε / p)) * p =
        ((103 / 50) * (17 / 10) + (10609 / 10000) * (289 / 200)) * ε := by
      field_simp
    rw [heq]
    linarith
  linarith

/-- Exact unit mean for both complex polynomial coefficients. -/
theorem sparseUnitPolynomial_mean {p : ℕ} [NeZero p]
    (E : Finset (ZMod p)) (hE : 0 ∉ E) (hsym : ∀ b, -b ∈ E ↔ b ∈ E)
    (hp : 1 < p) (c d : ℂ) :
    sparseUnitPolynomial p ((E.card : ℝ) / p) c d =
      ((p : ℂ) - 1)⁻¹ * ∑ x ∈ Finset.univ.erase 0,
        (1 + c * localSparseKernel E x + d * localSparseSquare E x) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hp1 : (p : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne')
  have hc : ((Finset.univ.erase (0 : ZMod p)).card : ℂ) = (p : ℂ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card,
      Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
  simp only [localSparseKernel, localSparseSquare]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sparseAdditiveKernel_sum_nonzero E hE, sparseAdditiveKernel_square_sum_nonzero E hsym]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hc]
  unfold sparseUnitPolynomial
  push_cast
  field_simp

/-- The scalar mean on the same polydisc as the operator has a uniform
`1+6/p` bound, independent of the dimension of the residue space. -/
theorem sparse_unit_polydisc_bound {p : ℕ} [Fact p.Prime]
    (E : Finset (ZMod p)) (hE : 0 ∉ E) (hsym : ∀ b, -b ∈ E ↔ b ∈ E)
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hcard : (E.card : ℝ) ≤ ε * p)
    (u v : ℂ) (hu : ‖u‖ ≤ 103 / 100) (hv : ‖v‖ ≤ 103 / 100) :
    ‖((p : ℂ) - 1)⁻¹ * ∑ x ∈ Finset.univ.erase 0,
      (1 + u * localSparseKernel E x) * (1 + v * localSparseKernel E x)‖ ≤
      1 + 6 / (p : ℝ) := by
  have hpNat : 1 < p := (Fact.out : p.Prime).one_lt
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have he (x : ZMod p) : (1 + u * localSparseKernel E x) * (1 + v * localSparseKernel E x) =
      1 + (u + v) * localSparseKernel E x + (u * v) * localSparseSquare E x := by
    unfold localSparseSquare
    ring
  simp_rw [he]
  rw [← sparseUnitPolynomial_mean E hE hsym hpNat]
  apply sparseUnitPolynomial_norm_le p ((E.card : ℝ) / p) ε (u + v) (u * v)
    (by exact_mod_cast (Fact.out : p.Prime).two_le) (by positivity)
    ((div_le_iff₀ hp0).mpr hcard) hε hε1
  · linarith [norm_add_le u v]
  · rw [norm_mul]
    have hh := mul_le_mul hu hv (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 103 / 100)
    norm_num at hh ⊢
    exact hh

end Ostmann

end OAI
