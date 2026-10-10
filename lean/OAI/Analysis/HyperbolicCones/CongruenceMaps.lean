import OAI.Analysis.HyperbolicCones.KernelSpectrum

namespace OAI

/-! Linear congruence maps and preservation of a two-block matrix pencil. -/

noncomputable section
open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix
namespace Paper256

def congruenceSym {n : ℕ} (S : Mat n ℝ) : Sym n →ₗ[ℝ] Sym n where
  toFun X := ⟨Sᵀ * (X : Mat n ℝ) * S, by
    change (Sᵀ * (X : Mat n ℝ) * S).IsHermitian
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_conjTranspose_mul_mul S (show (X : Mat n ℝ).IsHermitian from X.property)⟩
  map_add' X Y := by
    apply Subtype.ext
    change Sᵀ * ((X : Mat n ℝ) + (Y : Mat n ℝ)) * S =
      Sᵀ * (X : Mat n ℝ) * S + Sᵀ * (Y : Mat n ℝ) * S
    simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' r X := by
    apply Subtype.ext
    simp only [selfAdjoint.val_smul, RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]

@[simp] theorem congruenceSym_val {n : ℕ} (S : Mat n ℝ) (X : Sym n) :
    (congruenceSym S X : Mat n ℝ) = Sᵀ * (X : Mat n ℝ) * S := rfl

def congruenceRect {m n : ℕ} (S : Mat m ℝ) (T : Mat n ℝ) :
    Matrix (Fin m) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin m) (Fin n) ℝ where
  toFun A := Sᵀ * A * T
  map_add' A B := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' r A := by simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]

@[simp] theorem congruenceRect_apply {m n : ℕ} (S : Mat m ℝ) (T : Mat n ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) : congruenceRect S T A = Sᵀ * A * T := rfl

theorem congruenceSym_positive {n : ℕ} (S : Mat n ℝ) (X : Sym n)
    (hX : (X : Mat n ℝ).PosSemidef) : (congruenceSym S X : Mat n ℝ).PosSemidef := by
  simpa only [congruenceSym_val, conjTranspose_eq_transpose_of_trivial] using
    hX.conjTranspose_mul_mul_same S

theorem congruenceSym_inverseSquareRoot_self {n : ℕ} (H : Sym n)
    (hH : (H : Mat n ℝ).PosDef) : congruenceSym (inverseSquareRoot H) H = 1 := by
  apply Subtype.ext
  exact inverseSquareRoot_conjugate H hH

theorem block_congruence_identity {m n : ℕ} (S : Mat m ℝ) (T : Mat n ℝ)
    (A : Mat m ℝ) (B : Matrix (Fin m) (Fin n) ℝ) (D : Mat n ℝ) :
    (Matrix.fromBlocks S 0 0 T)ᵀ * Matrix.fromBlocks A B Bᵀ D *
        Matrix.fromBlocks S 0 0 T =
      Matrix.fromBlocks (Sᵀ * A * S) (Sᵀ * B * T)
        (Sᵀ * B * T)ᵀ (Tᵀ * D * T) := by
  simp only [Matrix.fromBlocks_transpose, transpose_zero, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, transpose_mul,
    transpose_transpose, Matrix.mul_assoc]

theorem block_congruence_posSemidef_iff {m n : ℕ} (S : Mat m ℝ) (T : Mat n ℝ)
    (hS : IsUnit S) (hT : IsUnit T)
    (A : Mat m ℝ) (B : Matrix (Fin m) (Fin n) ℝ) (D : Mat n ℝ) :
    (Matrix.fromBlocks (Sᵀ * A * S) (Sᵀ * B * T)
      (Sᵀ * B * T)ᵀ (Tᵀ * D * T)).PosSemidef ↔
      (Matrix.fromBlocks A B Bᵀ D).PosSemidef := by
  have hU : IsUnit (Matrix.fromBlocks S (0 : Matrix (Fin m) (Fin n) ℝ) 0 T) :=
    Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hS, hT⟩
  rw [← block_congruence_identity S T A B D]
  simpa only [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
    hU.posSemidef_star_left_conjugate_iff (x := Matrix.fromBlocks A B Bᵀ D)

end Paper256

end

end OAI
