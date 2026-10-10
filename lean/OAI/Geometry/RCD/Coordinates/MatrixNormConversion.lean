import OAI.Analysis.RCDHeat.Foundations
import Mathlib.Analysis.CStarAlgebra.Matrix

namespace OAI

/-! # Entry bounds and the Euclidean norm of coordinate transformations

Huang--Huang (2024), Theorem 4.1 uses the maximum of the absolute matrix
entries. The elementary dimension factor below converts that bound into
an operator bound before it is used in the coordinate construction.
-/

open scoped BigOperators InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

/-- A deliberately non-sharp dimension factor suffices: all smallness
parameters in the transformation theorem can be chosen after dimension. -/
theorem euclidean_operator_norm_le_of_entries {n : ℕ}
    (A : Euclidean n →L[ℝ] Euclidean n) {C : ℝ} (hC : 0 ≤ C)
    (hentry : ∀ i j, |A (EuclideanSpace.single j 1) i| ≤ C) :
    ‖A‖ ≤ (n : ℝ) ^ 2 * C := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hcolumn (j : Fin n) : ‖A (b j)‖ ≤ (n : ℝ) * C := by
    calc
      ‖A (b j)‖ = ‖∑ i, (A (b j)) i • b i‖ := by
        congr 1
        simpa only [b, EuclideanSpace.basisFun_repr] using (b.sum_repr (A (b j))).symm
      _ ≤ ∑ i, ‖(A (b j)) i • b i‖ := norm_sum_le _ _
      _ = ∑ i : Fin n, |A (EuclideanSpace.single j 1) i| := by
        simp [norm_smul, b]
      _ ≤ ∑ _i : Fin n, C := Finset.sum_le_sum fun i _ => hentry i j
      _ = (n : ℝ) * C := by simp
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (sq_nonneg _) hC)
  intro v
  calc
    ‖A v‖ = ‖∑ j, v j • A (b j)‖ := by
      have hv : v = ∑ j, v j • b j := by
        simpa only [b, EuclideanSpace.basisFun_repr] using (b.sum_repr v).symm
      calc
        ‖A v‖ = ‖A (∑ j, v j • b j)‖ := congrArg (fun x => ‖A x‖) hv
        _ = _ := by simp only [map_sum, map_smul]
    _ ≤ ∑ j, ‖v j • A (b j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin n, ‖v‖ * ((n : ℝ) * C) := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul]
      exact mul_le_mul (PiLp.norm_apply_le v j) (hcolumn j)
        (norm_nonneg _) (norm_nonneg _)
    _ = (n : ℝ) ^ 2 * C * ‖v‖ := by simp; ring

/-- An entrywise estimate on a published transformation matrix gives the
operator norm bound required by the metric iteration. -/
theorem matrix_euclidean_norm_le_of_entries {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hentry : ∀ i j, |A i j| ≤ C) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖ ≤ (n : ℝ) ^ 2 * C := by
  apply euclidean_operator_norm_le_of_entries _ hC
  intro i j
  simpa [Matrix.toEuclideanCLM_toLp, Matrix.mulVec, dotProduct] using hentry i j

/-- Near identity in the source's entry norm implies near identity in
Euclidean operator norm, with the dimension factor kept explicit. -/
theorem matrix_sub_id_norm_le_of_entries {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hentry : ∀ i j, |(A - 1) i j| ≤ epsilon) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A - ContinuousLinearMap.id ℝ (Euclidean n)‖ ≤
      (n : ℝ) ^ 2 * epsilon := by
  simpa only [map_sub, map_one,
    show (1 : Euclidean n →L[ℝ] Euclidean n) = ContinuousLinearMap.id ℝ _ from rfl] using
    matrix_euclidean_norm_le_of_entries (A - 1) hepsilon hentry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A near-identity invertible transformation has a controlled inverse;
no inverse bound needs to be separately supplied by the application. -/
theorem equiv_inverse_norm_le_of_sub_id (A : E ≃L[ℝ] E)
    {delta : ℝ} (hdelta1 : delta < 1)
    (hA : ‖(A : E →L[ℝ] E) - ContinuousLinearMap.id ℝ E‖ ≤ delta) :
    ‖(A.symm : E →L[ℝ] E)‖ ≤ (1 - delta)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr (by linarith))
  intro v
  have he := ((A : E →L[ℝ] E) - ContinuousLinearMap.id ℝ E).le_opNorm (A.symm v)
  simp only [sub_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.id_apply] at he
  have he' : ‖v - A.symm v‖ ≤ delta * ‖A.symm v‖ :=
    he.trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have ht := norm_sub_le v (v - A.symm v)
  rw [sub_sub_cancel] at ht
  have hh : (1 - delta) * ‖A.symm v‖ ≤ ‖v‖ := by linarith
  exact (le_inv_mul_iff₀ (by linarith : 0 < 1 - delta)).mpr hh

/-- The forward operator has the matching elementary bound. -/
theorem equiv_norm_le_of_sub_id (A : E ≃L[ℝ] E)
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hA : ‖(A : E →L[ℝ] E) - ContinuousLinearMap.id ℝ E‖ ≤ delta) :
    ‖(A : E →L[ℝ] E)‖ ≤ 1 + delta := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by linarith)
  intro v
  have he := ((A : E →L[ℝ] E) - ContinuousLinearMap.id ℝ E).le_opNorm v
  simp only [sub_apply, ContinuousLinearMap.id_apply] at he
  have he' := he.trans (mul_le_mul_of_nonneg_right hA (norm_nonneg v))
  change ‖A v - v‖ ≤ delta * ‖v‖ at he'
  have ht := norm_sub_le v (v - A v)
  rw [sub_sub_cancel, norm_sub_rev] at ht
  change ‖A v‖ ≤ (1 + delta) * ‖v‖
  calc
    ‖A v‖ ≤ ‖v‖ + ‖A v - v‖ := ht
    _ ≤ ‖v‖ + delta * ‖v‖ := add_le_add le_rfl he'
    _ = _ := by ring

end RegularPointCoordinates

end

end OAI
