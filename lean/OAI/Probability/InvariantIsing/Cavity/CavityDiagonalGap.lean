import OAI.Probability.InvariantIsing.Cavity.CavityPrecisionPath

namespace OAI

/-! The inverse-gap comparison for the diagonal covariances in the
finite-alphabet cavity recursion. -/

noncomputable section
open scoped Matrix

namespace InvariantIsing

lemma cavity_diagonal_inverse_gap {d : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (p s : Fin d → ℝ) (hs : ∀ i, 0 < s i) (hsp : ∀ i, s i ≤ p i)
    (hgap : (Matrix.diagonal (fun i => (p i)⁻¹) - K).PosDef) :
    (Matrix.diagonal (fun i => (s i)⁻¹) - K).PosDef := by
  have hd : (Matrix.diagonal (fun i => (s i)⁻¹ - (p i)⁻¹)).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    apply sub_nonneg.mpr
    simpa only [one_div] using one_div_le_one_div_of_le (hs i) (hsp i)
  have he : Matrix.diagonal (fun i => (s i)⁻¹) - K =
      (Matrix.diagonal (fun i => (p i)⁻¹) - K) +
        Matrix.diagonal (fun i => (s i)⁻¹ - (p i)⁻¹) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.diagonal_apply_ne _ hij]
  rw [he]
  exact hgap.add_posSemidef hd

lemma cavity_diagonal_gap_isUnit {d : ℕ} (K : Matrix (Fin d) (Fin d) ℝ)
    (p s : Fin d → ℝ) (hs : ∀ i, 0 < s i) (hsp : ∀ i, s i ≤ p i)
    (hgap : (Matrix.diagonal (fun i => (p i)⁻¹) - K).PosDef) :
    IsUnit (1 - Matrix.diagonal s * K).det := by
  have hg := cavity_diagonal_inverse_gap K p s hs hsp hgap
  have he : 1 - Matrix.diagonal s * K =
      Matrix.diagonal s * (Matrix.diagonal (fun i => (s i)⁻¹) - K) := by
    rw [mul_sub, Matrix.diagonal_mul_diagonal]
    have hone : Matrix.diagonal (fun i => s i * (s i)⁻¹) = 1 := by
      simp [funext fun i => mul_inv_cancel₀ (hs i).ne']
    rw [hone]
  rw [he, Matrix.det_mul]
  apply IsUnit.mul
  · exact isUnit_iff_ne_zero.mpr (Matrix.PosDef.diagonal hs).det_pos.ne'
  · exact isUnit_iff_ne_zero.mpr hg.det_pos.ne'

end InvariantIsing

end

end OAI
