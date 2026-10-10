import OAI.MeasureTheory.Falconer.Estimates.GeneralColumns

namespace OAI

/-! # A quantitative transverse frame for general-dimensional tube counting -/

namespace Falconer
open scoped BigOperators
variable {d : ℕ}

theorem euclideanColumnLinear_norm (v : Fin d → Space d) (hv : ∀ i, ‖v i‖ ≤ 1)
    (x : Space d) : ‖euclideanColumnLinear v x‖ ≤ (d:ℝ)*‖x‖ := by
  change ‖∑ i : Fin d, x i • v i‖ ≤ _
  calc
    _ ≤ ∑ i : Fin d, ‖x i • v i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin d, ‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact (mul_le_mul (PiLp.norm_apply_le x i) (hv i) (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_one _)
    _ = _ := by simp

theorem euclideanDualCoordinates_norm (v : Fin d → Space d) (hv : ∀ i, ‖v i‖ ≤ 1)
    (x : Space d) : ‖euclideanDualCoordinates v x‖ ≤
      ((d:ℝ)^2*(d.factorial:ℝ)/|(euclideanColumnMatrix v).det|)*‖x‖ := by
  let B : ℝ := (d.factorial:ℝ)/|(euclideanColumnMatrix v).det|
  have hB : 0 ≤ B := div_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
  have hM (i j : Fin d) : |euclideanColumnMatrix v i j| ≤ 1 :=
    (PiLp.norm_apply_le (v j) i).trans (hv j)
  have hi (i : Fin d) : |euclideanDualCoordinates v x i| ≤ (d:ℝ)*B*‖x‖ := by
    change |∑ j : Fin d, (euclideanColumnMatrix v)⁻¹ i j*x j| ≤ _
    calc
      _ ≤ ∑ j : Fin d, |(euclideanColumnMatrix v)⁻¹ i j*x j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin d, B*‖x‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul (unit_entry_inverse_bound _ hM i j) (PiLp.norm_apply_le x j) (abs_nonneg _) hB
      _ = _ := by simp [mul_assoc]
  have hh := coordinate_norm_le_card_mul (euclideanDualCoordinates v x) hi
  apply hh.trans_eq
  dsimp [B]
  ring

theorem exists_general_transverse_frame (v : Fin d → Space d) (hv : ∀ i, ‖v i‖ ≤ 1)
    {Δ : ℝ} (hΔ : 0 < Δ) (hgram : Δ ≤ Real.sqrt (Matrix.gram ℝ v).det) :
    ∃ e : Space d ≃L[ℝ] Space d,
      (∀ i, e (EuclideanSpace.basisFun (Fin d) ℝ i) = v i) ∧
      (∀ i j, j ≠ i → (e.symm (v i)) j = 0) ∧
      ‖e.toContinuousLinearMap‖ ≤ (d:ℝ) ∧
      ‖e.symm.toContinuousLinearMap‖ ≤ (d:ℝ)^2*(d.factorial:ℝ)/Δ := by
  rw [euclideanColumnMatrix_gram_sqrt] at hgram
  have hdet : (euclideanColumnMatrix v).det ≠ 0 := by
    intro hz
    rw [hz,abs_zero] at hgram
    linarith
  let e := euclideanColumnEquiv v hdet
  have he (i : Fin d) : e (EuclideanSpace.basisFun (Fin d) ℝ i) = v i := by
    change (∑ j : Fin d, (EuclideanSpace.basisFun (Fin d) ℝ i) j • v j) = v i
    simp
  refine ⟨e,he,?_,?_,?_⟩
  · intro i j hji
    rw [← he i,e.symm_apply_apply]
    simp [EuclideanSpace.basisFun_apply,hji]
  · apply e.toContinuousLinearMap.opNorm_le_bound (Nat.cast_nonneg _)
    exact euclideanColumnLinear_norm v hv
  · apply e.symm.toContinuousLinearMap.opNorm_le_bound (by positivity)
    intro x
    change ‖e.symm x‖ ≤ _
    rw [euclideanColumnEquiv_symm_apply]
    apply (euclideanDualCoordinates_norm v hv x).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact div_le_div_of_nonneg_left (by positivity) hΔ hgram

end Falconer

end OAI
