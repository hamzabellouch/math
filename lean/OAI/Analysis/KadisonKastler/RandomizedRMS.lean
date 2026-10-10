import OAI.Analysis.KadisonKastler.RandomizedRows

namespace OAI

/-! # Elementary norm bounds for finite random vectors -/

namespace KadisonKastler

open Finset
open scoped BigOperators

noncomputable section

variable {Ω H : Type*} [Fintype Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [InnerProductSpace ℂ H] in
/-- Finite root mean square is the normalized direct-sum norm. -/
theorem finiteRMS_eq_norm (v : Ω → H) :
    finiteRMS v = (Real.sqrt (Fintype.card Ω : ℝ))⁻¹ * ‖WithLp.toLp 2 v‖ := by
  unfold finiteRMS
  rw [Fintype.expect_eq_sum_div_card, Real.sqrt_div (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  rw [← PiLp.norm_sq_eq_of_L2, Real.sqrt_sq (norm_nonneg _)]
  exact div_eq_inv_mul _ _

omit [InnerProductSpace ℂ H] in
/-- Minkowski's inequality for the finite random vectors in the row construction. -/
theorem finiteRMS_add_le (v w : Ω → H) :
    finiteRMS (fun i => v i + w i) ≤ finiteRMS v + finiteRMS w := by
  rw [finiteRMS_eq_norm, finiteRMS_eq_norm, finiteRMS_eq_norm, ← mul_add]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  exact norm_add_le (WithLp.toLp 2 v) (WithLp.toLp 2 w)

omit [InnerProductSpace ℂ H] in
/-- A pointwise norm bound gives the same root mean square bound. -/
theorem finiteRMS_le_const [Nonempty Ω] (v : Ω → H) {C : ℝ}
    (hC : 0 ≤ C) (hv : ∀ i, ‖v i‖ ≤ C) : finiteRMS v ≤ C := by
  unfold finiteRMS
  apply (Real.sqrt_le_sqrt ?_).trans_eq (Real.sqrt_sq hC)
  calc
    (𝔼 i, ‖v i‖ ^ 2) ≤ (𝔼 _ : Ω, C ^ 2) :=
      expect_le_expect (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hv i) 2)
    _ = C ^ 2 := by simp

omit [InnerProductSpace ℂ H] in
/-- Pointwise norm domination passes through finite root mean squares. -/
theorem finiteRMS_mono (v w : Ω → H) (hv : ∀ i, ‖v i‖ ≤ ‖w i‖) :
    finiteRMS v ≤ finiteRMS w := by
  apply Real.sqrt_le_sqrt
  exact expect_le_expect (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hv i) 2)

omit [InnerProductSpace ℂ H] in
/-- Squaring finite root mean square recovers its average of squares. -/
theorem finiteRMS_sq (v : Ω → H) :
    (finiteRMS v) ^ 2 = 𝔼 i, ‖v i‖ ^ 2 :=
  Real.sq_sqrt (expect_nonneg (fun _ _ => sq_nonneg _))

variable {Θ I : Type*} [Fintype Θ] [Fintype I] [DecidableEq I] [Nonempty I]

/-- Orthogonal scalar phases and a uniform basis row preserve bounds
that already hold in root mean square over an independent random choice. -/
theorem phase_basis_double_rms_le {n : ℕ} [Nonempty Θ]
    (χ : I → Ω → ℂ)
    (hχ : ∀ i j, (𝔼 t, star (χ i t) * χ j t) = if i = j then 1 else 0)
    (v : I → Θ → Generator.FiniteHilbert (Fin n) H)
    {C : ℝ} (hC : 0 ≤ C) (hv : ∀ i, finiteRMS (v i) ≤ C) :
    finiteRMS (fun ta : (Θ × Ω) × Fin n => (Real.sqrt (n : ℝ)) •
      ((Real.sqrt (Fintype.card I : ℝ))⁻¹ •
        finitePhaseSum χ (fun i => v i ta.1.1) ta.1.2) ta.2) ≤ C := by
  unfold finiteRMS
  apply (Real.sqrt_le_sqrt ?_).trans_eq (Real.sqrt_sq hC)
  rw [← univ_product_univ, expect_product]
  simp_rw [basis_row_mean_square]
  rw [← univ_product_univ, expect_product]
  simp_rw [norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow]
  simp_rw [← mul_expect, Real.sq_sqrt (Nat.cast_nonneg _),
    finitePhaseSum_mean_square χ hχ]
  rw [expect_sum_comm]
  have hcard : 0 < (Fintype.card I : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  calc
    (Fintype.card I : ℝ)⁻¹ * ∑ i, (𝔼 θ, ‖v i θ‖ ^ 2) ≤
        (Fintype.card I : ℝ)⁻¹ * ∑ _ : I, C ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hcard.le)
      apply sum_le_sum
      intro i _
      rw [← finiteRMS_sq]
      exact pow_le_pow_left₀ (finiteRMS_nonneg _) (hv i) 2
    _ = C ^ 2 := by simp [hcard.ne']

end

end KadisonKastler

end OAI
