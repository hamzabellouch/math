import OAI.NumberTheory.TwoPoint.Bounds.MatrixSpectralTail

namespace OAI

/-! The trace spectral threshold also dominates the single-edge and
square-function scales needed for the noncommuting transfer. -/

namespace TwoPointCorrelations

lemma actual_spectral_scale_bounds (J : ℕ) (K W : ℝ) (hK : 0 ≤ K) (hW : 1 ≤ W) :
    let R := Real.exp 1 * (2 * (K * (2 * Real.exp 150 * Real.sqrt W) ^ J))
    0 ≤ R ∧ 2 * K ≤ R ∧ 4 * K ^ 2 * (8 * W) ^ J ≤ R ^ 2 := by
  dsimp only
  let C := 2 * Real.exp 150 * Real.sqrt W
  have hs : 1 ≤ Real.sqrt W := by simpa using Real.sqrt_le_sqrt hW
  have he : 2 ≤ Real.exp 150 := by linarith [Real.add_one_le_exp (150 : ℝ)]
  have hC : 1 ≤ C := by
    dsimp [C]
    nlinarith [Real.exp_pos (150 : ℝ)]
  have hCJ : 1 ≤ C ^ J := one_le_pow₀ hC
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hbase : 8 * W ≤ C ^ 2 := by
    have hW0 : 0 ≤ W := by linarith
    have hx : 0 ≤ (4 * (Real.exp 150) ^ 2 - 8) * W :=
      mul_nonneg (by nlinarith) hW0
    have hsq := Real.sq_sqrt hW0
    dsimp [C]
    nlinarith
  have hpower : (8 * W) ^ J ≤ (C ^ J) ^ 2 := by
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 8 * W) hbase J
    simpa only [← pow_mul, Nat.mul_comm 2 J] using hp
  have hlarge : 2 * K * C ^ J ≤ Real.exp 1 * (2 * (K * C ^ J)) := by
    have hp := mul_le_mul_of_nonneg_right he1 (show 0 ≤ 2 * (K * C ^ J) by positivity)
    simpa only [one_mul, mul_assoc] using hp
  refine ⟨by positivity, ?_, ?_⟩
  · exact (le_mul_of_one_le_right (by positivity : 0 ≤ 2 * K) hCJ).trans hlarge
  · calc
      4 * K ^ 2 * (8 * W) ^ J ≤ (2 * K * C ^ J) ^ 2 := by
        have hp := mul_le_mul_of_nonneg_left hpower (show 0 ≤ 4 * K ^ 2 by positivity)
        nlinarith
      _ ≤ _ := (sq_le_sq₀ (by positivity) (by positivity)).mpr hlarge

end TwoPointCorrelations

end OAI
