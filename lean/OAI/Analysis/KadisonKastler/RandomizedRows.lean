import OAI.Analysis.KadisonKastler.RandomizedPairing

namespace OAI

/-! # The mean-square normalization of the randomized rows -/

namespace KadisonKastler

open Finset
open scoped BigOperators

noncomputable section

variable {H Ω I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [Fintype Ω] [Fintype I] [DecidableEq I] [Nonempty I]

/-- Normalizing a finite orthogonal phase sum removes its number of
terms from the mean square. -/
theorem normalized_phase_mean_square (χ : I → Ω → ℂ)
    (hχ : ∀ i j, (𝔼 t, star (χ i t) * χ j t) = if i = j then 1 else 0)
    (v : I → H) (x : H) (hv : ∀ i, ‖v i‖ = ‖x‖) :
    (𝔼 t, ‖(Real.sqrt (Fintype.card I : ℝ))⁻¹ • finitePhaseSum χ v t‖ ^ 2) = ‖x‖ ^ 2 := by
  have hcard : (Fintype.card I : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp_rw [norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow]
  rw [← mul_expect, Real.sq_sqrt (Nat.cast_nonneg _), finitePhaseSum_mean_square χ hχ]
  simp only [hv, sum_const, card_univ, nsmul_eq_mul]
  rw [inv_mul_cancel_left₀ hcard]

variable {n : ℕ}

/-- Averaging a uniformly chosen basis row, with the factor `sqrt n`,
preserves the Hilbert direct-sum norm exactly. -/
theorem basis_row_mean_square (x : Generator.FiniteHilbert (Fin n) H) :
    (𝔼 a : Fin n, ‖(Real.sqrt (n : ℝ)) • x a‖ ^ 2) = ‖x‖ ^ 2 := by
  simp_rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
  rw [Real.sq_sqrt (Nat.cast_nonneg _), ← mul_expect]
  calc
    _ = ∑ a : Fin n, ‖x a‖ ^ 2 := by
      simpa only [Fintype.card_fin] using Fintype.card_mul_expect (fun a : Fin n => ‖x a‖ ^ 2)
    _ = _ := (PiLp.norm_sq_eq_of_L2 (fun _ : Fin n => H) x).symm

/-- Independent choice of a phase and a basis row produces a row family
of mean-square norm exactly that of the original vector. -/
theorem phase_basis_row_mean_square (χ : I → Ω → ℂ)
    (hχ : ∀ i j, (𝔼 t, star (χ i t) * χ j t) = if i = j then 1 else 0)
    (v : I → Generator.FiniteHilbert (Fin n) H)
    (x : Generator.FiniteHilbert (Fin n) H) (hv : ∀ i, ‖v i‖ = ‖x‖) :
    (𝔼 ta : Ω × Fin n,
      ‖(Real.sqrt (n : ℝ)) •
        ((Real.sqrt (Fintype.card I : ℝ))⁻¹ • finitePhaseSum χ v ta.1) ta.2‖ ^ 2) = ‖x‖ ^ 2 := by
  have he := expect_product (univ : Finset Ω) (univ : Finset (Fin n))
    (fun ta : Ω × Fin n => ‖(Real.sqrt (n : ℝ)) •
      ((Real.sqrt (Fintype.card I : ℝ))⁻¹ • finitePhaseSum χ v ta.1) ta.2‖ ^ 2)
  rw [univ_product_univ] at he
  rw [he]
  simp_rw [basis_row_mean_square]
  exact normalized_phase_mean_square χ hχ v x hv

end

end KadisonKastler

end OAI
