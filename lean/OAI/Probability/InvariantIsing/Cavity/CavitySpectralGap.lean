import OAI.Probability.InvariantIsing.Cavity.CavityStepPrecision

namespace OAI

/-! The upper spectral gap supplies the diagonal inverse-gap hypothesis
used by the quadratic cavity recursion. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

lemma cavity_upper_spectral_gap {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (L b : ℝ) (hA : (L • (1 : Matrix (Fin d) (Fin d) ℝ) - A).PosSemidef)
    (hb : L < b) : (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A).PosDef := by
  have hp : ((b - L) • (1 : Matrix (Fin d) (Fin d) ℝ)).PosDef :=
    Matrix.PosDef.one.smul (sub_pos.mpr hb)
  have he : b • (1 : Matrix (Fin d) (Fin d) ℝ) - A =
      (b - L) • (1 : Matrix (Fin d) (Fin d) ℝ) + (L • 1 - A) := by module
  rw [he]
  exact hp.add_posSemidef hA

lemma cavity_resolvent_diagonal_gap {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (eig : Fin d → ℝ) (L b : ℝ)
    (hA : (L • (1 : Matrix (Fin d) (Fin d) ℝ) - A).PosSemidef) (hb : L < b) :
    (Matrix.diagonal (fun i => (((b - eig i)⁻¹)⁻¹)) -
      (A - Matrix.diagonal eig)).PosDef := by
  have he : Matrix.diagonal (fun i => (((b - eig i)⁻¹)⁻¹)) -
      (A - Matrix.diagonal eig) = b • (1 : Matrix (Fin d) (Fin d) ℝ) - A := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [inv_inv, Matrix.sub_apply, Matrix.diagonal_apply_eq,
        Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      ring
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  rw [he]
  exact cavity_upper_spectral_gap A L b hA hb

/-- A nonterminal step, where both resolvents have positive arguments. -/
theorem cavity_resolvent_step_precision {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℝ) (eig : Fin d → ℝ) (L b₀ b₁ : ℝ)
    (hK : (A - Matrix.diagonal eig).transpose = A - Matrix.diagonal eig)
    (hA : (L • (1 : Matrix (Fin d) (Fin d) ℝ) - A).PosSemidef)
    (heig : ∀ i, eig i ≤ L) (hb₀ : L < b₀) (hb₁ : b₀ ≤ b₁)
    (hB : Matrix.diagonal (fun i => (b₀ - eig i)⁻¹) -
      Matrix.diagonal (fun i => (b₁ - eig i)⁻¹) = B * B.transpose) :
    (cavityFactorPrecision
      (cavityBackwardQuadratic (A - Matrix.diagonal eig)
        (Matrix.diagonal (fun i => (b₁ - eig i)⁻¹))) B).PosDef := by
  apply cavity_step_precision_posDef (A - Matrix.diagonal eig) B hK
    (fun i => (b₀ - eig i)⁻¹) (fun i => (b₁ - eig i)⁻¹)
  · intro i
    exact inv_pos.mpr (sub_pos.mpr (lt_of_le_of_lt (heig i) hb₀))
  · intro i
    exact (inv_pos.mpr (sub_pos.mpr (lt_of_le_of_lt (heig i) (hb₀.trans_le hb₁)))).le
  · intro i
    simpa only [one_div] using one_div_le_one_div_of_le
      (sub_pos.mpr (lt_of_le_of_lt (heig i) hb₀)) (sub_le_sub_right hb₁ (eig i))
  · right
    intro i
    exact inv_pos.mpr (sub_pos.mpr (lt_of_le_of_lt (heig i) (hb₀.trans_le hb₁)))
  · exact cavity_resolvent_diagonal_gap A eig L b₀ hA hb₀
  · exact hB

/-- The residual endpoint has lower covariance zero. -/
theorem cavity_resolvent_terminal_precision {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℝ) (eig : Fin d → ℝ) (L b : ℝ)
    (hK : (A - Matrix.diagonal eig).transpose = A - Matrix.diagonal eig)
    (hA : (L • (1 : Matrix (Fin d) (Fin d) ℝ) - A).PosSemidef)
    (heig : ∀ i, eig i ≤ L) (hb : L < b)
    (hB : Matrix.diagonal (fun i => (b - eig i)⁻¹) = B * B.transpose) :
    (cavityFactorPrecision (A - Matrix.diagonal eig) B).PosDef := by
  have hp : ∀ i, 0 < (b - eig i)⁻¹ := fun i =>
    inv_pos.mpr (sub_pos.mpr (lt_of_le_of_lt (heig i) hb))
  have h := cavity_step_precision_posDef (A - Matrix.diagonal eig) B hK
    (fun i => (b - eig i)⁻¹) (fun _ => 0) hp (by intro i; exact le_rfl)
    (by intro i; exact (hp i).le) (Or.inl (by intro i; rfl))
    (cavity_resolvent_diagonal_gap A eig L b hA hb) (by simpa using hB)
  simpa only [Matrix.diagonal_zero, cavityBackwardQuadratic_zero] using h

end InvariantIsing

end

end OAI
