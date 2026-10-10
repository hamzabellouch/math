import OAI.GroupTheory.PolycyclicRecognition.Geometry.TriangularProducts
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OAI

/-!
# Actual logarithmic height on positive triangular matrices

The logarithms of positive diagonal entries form a group homomorphism.
Bounded logarithmic height bounds both diagonal frames and their inverses,
which are the hypotheses in the polynomial product estimate.
-/

namespace PolycyclicRecognition

open scoped Matrix.Norms.Operator

variable {n : ℕ}

theorem triangular_mul_diag (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular) (i : Fin n) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · simp

/-- Positive invertible upper triangular real matrices, as an actual subgroup. -/
def positiveTriangular (n : ℕ) : Subgroup (Matrix (Fin n) (Fin n) ℝ)ˣ where
  carrier := {u | (u : Matrix (Fin n) (Fin n) ℝ).IsUpperTriangular ∧
    ∀ i, 0 < (u : Matrix (Fin n) (Fin n) ℝ) i i}
  one_mem' := by
    refine ⟨?_, ?_⟩
    · intro i j hij
      exact Matrix.one_apply_ne (ne_of_gt hij)
    · intro i
      simp
  mul_mem' := by
    intro a b ha hb
    refine ⟨ha.1.mul hb.1, ?_⟩
    intro i
    change 0 < ((a : Matrix (Fin n) (Fin n) ℝ) * (b : Matrix (Fin n) (Fin n) ℝ)) i i
    rw [triangular_mul_diag _ _ ha.1 hb.1]
    exact mul_pos (ha.2 i) (hb.2 i)
  inv_mem' := by
    intro a ha
    have hu : (↑a⁻¹ : Matrix (Fin n) (Fin n) ℝ).IsUpperTriangular := by
      rw [Matrix.coe_units_inv]
      exact Matrix.blockTriangular_inv_of_blockTriangular ha.1
    refine ⟨hu, fun i => ?_⟩
    have hi : (a : Matrix (Fin n) (Fin n) ℝ) i i *
        (↑a⁻¹ : Matrix (Fin n) (Fin n) ℝ) i i = 1 := by
      rw [← triangular_mul_diag _ _ ha.1 hu, Units.mul_inv]
      simp
    exact (mul_pos_iff_of_pos_left (ha.2 i)).mp (hi ▸ zero_lt_one)

namespace PositiveTriangular

abbrev matrix (g : positiveTriangular n) : Matrix (Fin n) (Fin n) ℝ := g.val

theorem upper (g : positiveTriangular n) : (matrix g).IsUpperTriangular := g.property.1

theorem diagonal_pos (g : positiveTriangular n) (i : Fin n) : 0 < matrix g i i := g.property.2 i

/-- The diagonal characters with their actual unit values. -/
noncomputable def diagonal : positiveTriangular n →* (Fin n → ℝˣ) where
  toFun g i := Units.mk0 (matrix g i i) (diagonal_pos g i).ne'
  map_one' := by
    ext i
    simp [matrix]
  map_mul' g h := by
    ext i
    exact triangular_mul_diag (matrix g) (matrix h) (upper g) (upper h) i

@[simp] theorem diagonal_val (g : positiveTriangular n) (i : Fin n) :
    (diagonal g i : ℝ) = matrix g i i := rfl

/-- The logarithmic diagonal is a homomorphism to an additive real vector space. -/
noncomputable def height : positiveTriangular n →* Multiplicative (Fin n → ℝ) where
  toFun g := Multiplicative.ofAdd fun i => Real.log (matrix g i i)
  map_one' := by
    apply Multiplicative.ext
    funext i
    simp [matrix]
  map_mul' g h := by
    apply Multiplicative.ext
    funext i
    change Real.log (matrix (g * h) i i) = Real.log (matrix g i i) + Real.log (matrix h i i)
    change Real.log ((matrix g * matrix h) i i) = _
    rw [triangular_mul_diag _ _ (upper g) (upper h),
      Real.log_mul (diagonal_pos g i).ne' (diagonal_pos h i).ne']

@[simp] theorem height_apply (g : positiveTriangular n) (i : Fin n) :
    (height g).toAdd i = Real.log (matrix g i i) := rfl

/-- The exact diagonal frame used to normalize triangular products. -/
noncomputable def frame (g : positiveTriangular n) : (Matrix (Fin n) (Fin n) ℝ)ˣ :=
  diagonalUnit (diagonal g)

/-- A bounded height bounds the frame and its inverse by the same exponential. -/
theorem frame_norm_le_exp (g : positiveTriangular n) {M : ℝ}
    (hg : ‖(height g).toAdd‖ ≤ M) :
    ‖(frame g : Matrix (Fin n) (Fin n) ℝ)‖ ≤ Real.exp M ∧
    ‖(↑(frame g)⁻¹ : Matrix (Fin n) (Fin n) ℝ)‖ ≤ Real.exp M := by
  have hi (i : Fin n) : |Real.log (matrix g i i)| ≤ M :=
    (norm_le_pi_norm ((height g).toAdd) i).trans hg
  constructor
  · change ‖Matrix.diagonal (fun i => (diagonal g i : ℝ))‖ ≤ _
    rw [Matrix.linfty_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (Real.exp_pos M).le).mpr
    intro i
    rw [diagonal_val, Real.norm_eq_abs, abs_of_pos (diagonal_pos g i)]
    calc
      matrix g i i = Real.exp (Real.log (matrix g i i)) := (Real.exp_log (diagonal_pos g i)).symm
      _ ≤ Real.exp M := Real.exp_le_exp.mpr (le_trans (le_abs_self _) (hi i))
  · change ‖Matrix.diagonal (fun i => (↑(diagonal g i)⁻¹ : ℝ))‖ ≤ _
    rw [Matrix.linfty_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (Real.exp_pos M).le).mpr
    intro i
    change ‖(matrix g i i)⁻¹‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (diagonal_pos g i))]
    calc
      (matrix g i i)⁻¹ = Real.exp (-Real.log (matrix g i i)) := by
        rw [Real.exp_neg, Real.exp_log (diagonal_pos g i)]
      _ ≤ Real.exp M := Real.exp_le_exp.mpr (le_trans (neg_le_abs _) (hi i))

end PositiveTriangular
end PolycyclicRecognition

end OAI
