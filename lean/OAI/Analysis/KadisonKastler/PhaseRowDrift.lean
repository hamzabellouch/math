import OAI.Analysis.KadisonKastler.RandomizedRows
import OAI.Analysis.KadisonKastler.ClippedLimits

namespace OAI

/-! # Passing the coefficient drift bounds to the randomized rows -/

namespace KadisonKastler

open Finset Filter
open scoped BigOperators Topology

noncomputable section

variable {H Ω I J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [Fintype Ω] [Fintype I] [DecidableEq I] [Nonempty I]

/-- The normalized orthogonal phase sum preserves a uniform bound on
its terms in mean square, independently of the number of terms. -/
theorem normalized_phase_mean_square_le (χ : I → Ω → ℂ)
    (hχ : ∀ i j, (𝔼 t, star (χ i t) * χ j t) = if i = j then 1 else 0)
    (v : I → H) {C : ℝ} (hv : ∀ i, ‖v i‖ ≤ C) :
    (𝔼 t, ‖(Real.sqrt (Fintype.card I : ℝ))⁻¹ • finitePhaseSum χ v t‖ ^ 2) ≤ C ^ 2 := by
  have hcard : (0 : ℝ) < Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  simp_rw [norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow]
  rw [← mul_expect, Real.sq_sqrt hcard.le, finitePhaseSum_mean_square χ hχ]
  calc
    _ ≤ (Fintype.card I : ℝ)⁻¹ * ∑ _ : I, C ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hcard.le)
      exact sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hv i) 2
    _ = C ^ 2 := by simp [hcard.ne']

/-- The subsequent choice of a basis row also preserves that uniform
mean-square bound. -/
theorem phase_basis_row_drift_le {n : ℕ} (χ : I → Ω → ℂ)
    (hχ : ∀ i j, (𝔼 t, star (χ i t) * χ j t) = if i = j then 1 else 0)
    (v : I → Generator.FiniteHilbert (Fin n) H)
    {C : ℝ} (hC : 0 ≤ C) (hv : ∀ i, ‖v i‖ ≤ C) :
    finiteRMS (fun ta : Ω × Fin n => (Real.sqrt (n : ℝ)) •
      ((Real.sqrt (Fintype.card I : ℝ))⁻¹ • finitePhaseSum χ v ta.1) ta.2) ≤ C := by
  unfold finiteRMS
  have he := expect_product (univ : Finset Ω) (univ : Finset (Fin n))
    (fun ta : Ω × Fin n => ‖(Real.sqrt (n : ℝ)) •
      ((Real.sqrt (Fintype.card I : ℝ))⁻¹ • finitePhaseSum χ v ta.1) ta.2‖ ^ 2)
  rw [univ_product_univ] at he
  rw [he]
  simp_rw [basis_row_mean_square]
  exact (Real.sqrt_le_sqrt (normalized_phase_mean_square_le χ hχ v hv)).trans_eq
    (Real.sqrt_sq hC)

/-- Finitely many eventual power-drift estimates pass to the row drift
with no loss depending on the number of powers or the matrix size. -/
theorem eventually_phase_basis_row_drift_le {n : ℕ} (l : Filter J)
    (χ : I → Ω → ℂ)
    (hχ : ∀ i j, (𝔼 t, star (χ i t) * χ j t) = if i = j then 1 else 0)
    (v : J → I → Generator.FiniteHilbert (Fin n) H)
    {C : ℝ} (hC : 0 ≤ C)
    (hv : ∀ i, ∀ ε > 0, ∀ᶠ j in l, ‖v j i‖ ≤ C + ε) :
    ∀ ε > 0, ∀ᶠ j in l,
      finiteRMS (fun ta : Ω × Fin n => (Real.sqrt (n : ℝ)) •
        ((Real.sqrt (Fintype.card I : ℝ))⁻¹ • finitePhaseSum χ (v j) ta.1) ta.2) ≤ C + ε := by
  intro ε hε
  have he : ∀ᶠ j in l, ∀ i, ‖v j i‖ ≤ C + ε :=
    eventually_all.mpr (fun i => hv i ε hε)
  filter_upwards [he] with j hj
  exact phase_basis_row_drift_le χ hχ (v j) (by positivity) hj

end

end KadisonKastler

end OAI
