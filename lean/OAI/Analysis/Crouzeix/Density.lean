import Mathlib
import OAI.Analysis.Crouzeix.BoundaryOperators

namespace OAI

/-! Density. -/

noncomputable section

open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

open MeasureTheory

namespace CrouzeixHilbert.Boundary

section Equality

variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem eq_of_norm_le_inner (u v : H) (hn : ‖u‖ ≤ ‖v‖)
    (hi : ⟪v, u⟫_ℂ = ⟪v, v⟫_ℂ) : u = v := by
  have he : RCLike.re ⟪u, v⟫_ℂ = ‖v‖ ^ 2 := by
    rw [inner_re_symm, hi, ← norm_sq_eq_re_inner]
  have hd := norm_sub_sq (𝕜 := ℂ) u v
  rw [he] at hd
  have hz : ‖u - v‖ = 0 := by
    nlinarith only [hd, hn, norm_nonneg u, norm_nonneg v, norm_nonneg (u - v), sq_nonneg ‖u - v‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

variable [CompleteSpace E] [CompleteSpace H]

theorem adjoint_eq_of_contraction (M : E →L[ℂ] H) (hM : ‖M‖ ≤ 1)
    (x : E) (y : H) (hxy : M x = y) (hn : ‖x‖ = ‖y‖) :
    ContinuousLinearMap.adjoint M y = x := by
  apply eq_of_norm_le_inner
  · calc
      ‖(ContinuousLinearMap.adjoint M) y‖ ≤ ‖ContinuousLinearMap.adjoint M‖ * ‖y‖ :=
        (ContinuousLinearMap.adjoint M).le_opNorm y
      _ = ‖M‖ * ‖y‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
      _ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right hM (norm_nonneg _)
      _ = ‖x‖ := by rw [one_mul, hn]
  · rw [ContinuousLinearMap.adjoint_inner_right, hxy, inner_self_eq_norm_sq_to_K,
      inner_self_eq_norm_sq_to_K, hn]

theorem equality_in_compression (V : E →ₗᵢ[ℂ] H) (M : H →L[ℂ] H)
    (hM : ‖M‖ ≤ 1) (x y : E) (hn : ‖x‖ = ‖y‖)
    (hxy : ContinuousLinearMap.adjoint V.toContinuousLinearMap (M (V x)) = y) :
    M (V x) = V y ∧ ContinuousLinearMap.adjoint M (V y) = V x := by
  have hf : M (V x) = V y := by
    apply eq_of_norm_le_inner
    · calc
        ‖M (V x)‖ ≤ ‖M‖ * ‖V x‖ := M.le_opNorm _
        _ ≤ 1 * ‖V x‖ := mul_le_mul_of_nonneg_right hM (norm_nonneg _)
        _ = ‖V y‖ := by simp only [one_mul, V.norm_map, hn]
    · change ⟪V.toContinuousLinearMap y, M (V x)⟫_ℂ = ⟪V y, V y⟫_ℂ
      rw [← V.toContinuousLinearMap.adjoint_inner_right, hxy, V.inner_map_map]
  exact ⟨hf, adjoint_eq_of_contraction M hM (V x) (V y) hf (by
    simpa only [V.norm_map] using hn)⟩

end Equality

section PartialTraces

variable {n m : Type*} [Fintype n]

def crossPartialTrace (X Y : Matrix n m ℂ) : Matrix m m ℂ :=
  (Xᴴ * Y)ᵀ

theorem crossPartialTrace_apply (X Y : Matrix n m ℂ) (j k : m) :
    crossPartialTrace X Y j k = ∑ a, Y a j * star (X a k) := by
  simp only [crossPartialTrace, Matrix.transpose_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

@[simp] theorem crossPartialTrace_conjTranspose (X Y : Matrix n m ℂ) :
    (crossPartialTrace X Y)ᴴ = crossPartialTrace Y X := by
  ext j k
  simp only [Matrix.conjTranspose_apply, crossPartialTrace_apply, star_sum,
    star_mul, star_star]

variable [Fintype m]

theorem crossPartialTrace_self_posSemidef (X : Matrix n m ℂ) :
    (crossPartialTrace X X).PosSemidef := by
  exact (Matrix.posSemidef_conjTranspose_mul_self X).transpose

theorem crossPartialTrace_block_posSemidef (X Y : Matrix n m ℂ) :
    (Matrix.fromBlocks (crossPartialTrace X X) (crossPartialTrace Y X)
      (crossPartialTrace X Y) (crossPartialTrace Y Y)).PosSemidef := by
  have h := (Matrix.posSemidef_conjTranspose_mul_self (Matrix.fromCols X Y)).transpose
  have he : Matrix.fromBlocks (crossPartialTrace X X) (crossPartialTrace Y X)
      (crossPartialTrace X Y) (crossPartialTrace Y Y) =
      ((Matrix.fromCols X Y)ᴴ * Matrix.fromCols X Y)ᵀ := by
    ext i j
    cases i <;> cases j <;> rfl
  rw [he]
  exact h

theorem crossPartialTrace_ordered (X Y : Matrix n m ℂ) (F : Matrix m m ℂ)
    (hforward : Y = X * Fᵀ) (hadjoint : X = Y * (Fᴴ)ᵀ) :
    crossPartialTrace X X = Fᴴ * crossPartialTrace X Y ∧
    crossPartialTrace X Y = F * crossPartialTrace X X ∧
    crossPartialTrace Y Y = crossPartialTrace X Y * Fᴴ := by
  refine ⟨?_, ?_, ?_⟩
  · change (Xᴴ * X)ᵀ = Fᴴ * (Xᴴ * Y)ᵀ
    nth_rw 2 [hadjoint]
    rw [← Matrix.mul_assoc, Matrix.transpose_mul, Matrix.transpose_transpose]
  · change (Xᴴ * Y)ᵀ = F * (Xᴴ * X)ᵀ
    rw [hforward, ← Matrix.mul_assoc, Matrix.transpose_mul, Matrix.transpose_transpose]
  · change (Yᴴ * Y)ᵀ = (Xᴴ * Y)ᵀ * Fᴴ
    nth_rw 1 [hforward]
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.transpose_mul]
    congr 1

def weightedPartialTrace (E : Matrix n n ℂ) (X Y : Matrix n m ℂ) : Matrix m m ℂ :=
  (Xᴴ * E * Y)ᵀ

omit [Fintype m] in
theorem weightedPartialTrace_factor (L : Matrix n n ℂ) (X Y : Matrix n m ℂ) :
    weightedPartialTrace (Lᴴ * L) X Y = crossPartialTrace (L * X) (L * Y) := by
  simp only [weightedPartialTrace, crossPartialTrace, Matrix.conjTranspose_mul, Matrix.mul_assoc]

variable [DecidableEq n]

theorem weightedPartialTrace_block_posSemidef (E : Matrix n n ℂ)
    (hE : E.PosSemidef) (X Y : Matrix n m ℂ) :
    (Matrix.fromBlocks (weightedPartialTrace E X X) (weightedPartialTrace E Y X)
      (weightedPartialTrace E X Y) (weightedPartialTrace E Y Y)).PosSemidef := by
  obtain ⟨L, hL⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hE.nonneg
  rw [hL]
  simpa only [Matrix.star_eq_conjTranspose, weightedPartialTrace_factor] using
    crossPartialTrace_block_posSemidef (L * X) (L * Y)

end PartialTraces

end CrouzeixHilbert.Boundary

end

end OAI
