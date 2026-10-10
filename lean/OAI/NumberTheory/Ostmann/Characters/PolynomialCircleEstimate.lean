import OAI.NumberTheory.Ostmann.Preliminaries.FinitePolynomialTail

namespace OAI

/-! # Cauchy and truncation estimates for ordinary finite polynomials -/

namespace Ostmann
open scoped Classical BigOperators

theorem sum_zmod_val {N : ℕ} [NeZero N] {E : Type*} [AddCommMonoid E]
    (f : ℕ → E) : (∑ j : ZMod N, f j.val) = ∑ j ∈ Finset.range N, f j := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => exact Fin.sum_univ_eq_sum_range f (n + 1)

noncomputable def finitePolynomial {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (c : ℕ → E) (N : ℕ) (u : ℂ) : E := ∑ i ∈ Finset.range N, u ^ i • c i

theorem cyclicPolynomial_eq_finitePolynomial {N : ℕ} [NeZero N]
    {E : Type*} [AddCommGroup E] [Module ℂ E] (c : ℕ → E) (r : ℝ) (z : ZMod N) :
    cyclicPolynomial (fun i : ZMod N => c i.val) r z =
      finitePolynomial c N ((r : ℂ) * ZMod.stdAddChar z) := by
  have hc (i : ZMod N) : ZMod.stdAddChar (i * z) = ZMod.stdAddChar z ^ i.val := by
    calc
      _ = ZMod.stdAddChar ((i.val : ZMod N) * z) := by rw [ZMod.natCast_zmod_val]
      _ = _ := by rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]
  unfold cyclicPolynomial finitePolynomial
  calc
    _ = ∑ i : ZMod N, (((r : ℂ) * ZMod.stdAddChar z) ^ i.val) • c i.val := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hc, smul_smul, mul_pow, Complex.ofReal_pow, mul_comm]
    _ = _ := sum_zmod_val (N := N) (fun i => (((r : ℂ) * ZMod.stdAddChar z) ^ i) • c i)

noncomputable def finitePolynomial₂ {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (c : ℕ → ℕ → E) (N : ℕ) (u v : ℂ) : E :=
  finitePolynomial (fun i => finitePolynomial (c i) N v) N u

theorem finitePolynomial₂_coefficient_norm_le {N : ℕ} [NeZero N]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c : ℕ → ℕ → E) (r M : ℝ) (hr : 0 < r)
    (hM : ∀ u v : ℂ, ‖u‖ = r → ‖v‖ = r → ‖finitePolynomial₂ c N u v‖ ≤ M)
    (i j : ℕ) (hi : i < N) (hj : j < N) :
    ‖c i j‖ ≤ M / r ^ i / r ^ j := by
  have hn (z : ZMod N) : ‖(r : ℂ) * ZMod.stdAddChar z‖ = r := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      ZMod.stdAddChar_apply, Circle.norm_coe, mul_one]
  have hgrid (z w : ZMod N) :
      ‖cyclicPolynomial (fun i : ZMod N =>
        cyclicPolynomial (fun j : ZMod N => c i.val j.val) r w) r z‖ ≤ M := by
    simp_rw [cyclicPolynomial_eq_finitePolynomial]
    rw [cyclicPolynomial_eq_finitePolynomial
      (fun i => finitePolynomial (c i) N ((r : ℂ) * ZMod.stdAddChar w)) r z]
    exact hM _ _ (hn z) (hn w)
  have hh := cyclicPolynomial_two_coefficient_norm_le
    (fun i j : ZMod N => c i.val j.val) r M hr hgrid (i : ZMod N) (j : ZMod N)
  simpa only [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] using hh

theorem finitePolynomial₂_truncation_error {N : ℕ} [NeZero N]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c : ℕ → ℕ → E) (r M : ℝ) (hr : 1 < r) (hM0 : 0 ≤ M)
    (hM : ∀ u v : ℂ, ‖u‖ = r → ‖v‖ = r → ‖finitePolynomial₂ c N u v‖ ≤ M)
    (K : ℕ) :
    ‖finitePolynomial₂ c N 1 1 - rectangularPolynomialSum c N K‖ ≤
      2 * M * r⁻¹ ^ (K + 1) / (1 - r⁻¹) ^ 2 := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hc (i : ℕ) (hi : i < N) (j : ℕ) (hj : j < N) :
      ‖c i j‖ ≤ M * r⁻¹ ^ i * r⁻¹ ^ j := by
    simpa only [div_eq_mul_inv, inv_pow] using
      finitePolynomial₂_coefficient_norm_le c r M hr0 hM i j hi hj
  simpa only [finitePolynomial₂, finitePolynomial, one_pow, one_smul] using
    rectangularPolynomialSum_error c N K M r⁻¹ hM0 (inv_nonneg.mpr hr0.le)
      ((inv_lt_one₀ hr0).mpr hr) hc

theorem finitePolynomial₂_coefficient_unique {N : ℕ} [NeZero N]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c d : ℕ → ℕ → E)
    (h : ∀ u v, finitePolynomial₂ c N u v = finitePolynomial₂ d N u v)
    (i j : ℕ) (hi : i < N) (hj : j < N) : c i j = d i j := by
  have hz (u v : ℂ) : finitePolynomial₂ (fun i j => c i j - d i j) N u v = 0 := by
    simp only [finitePolynomial₂, finitePolynomial, smul_sub, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (h u v)
  have hc := finitePolynomial₂_coefficient_norm_le (fun i j => c i j - d i j)
    1 0 (by norm_num) (by intro u v _ _; rw [hz]; simp) i j hi hj
  have he : c i j - d i j = 0 := norm_le_zero_iff.mp (by simpa using hc)
  exact sub_eq_zero.mp he

end Ostmann

end OAI
