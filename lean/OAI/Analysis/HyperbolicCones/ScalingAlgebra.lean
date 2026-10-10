import OAI.Analysis.HyperbolicCones.PencilBlocks

namespace OAI

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

universe u

namespace Paper256

def blockScalar (a c : ℕ) (s : ℝ) :
    Matrix (Fin a ⊕ Fin c) (Fin a ⊕ Fin c) ℝ :=
  Matrix.fromBlocks 1 0 0 (s • (1 : Mat c ℝ))

theorem blockScalar_transpose (a c : ℕ) (s : ℝ) :
    (blockScalar a c s)ᵀ = blockScalar a c s := by
  simp [blockScalar, Matrix.fromBlocks_transpose]

theorem blockScalar_isUnit (a c : ℕ) (s : ℝ) (hs : s ≠ 0) :
    IsUnit (blockScalar a c s) := by
  refine ⟨⟨blockScalar a c s, blockScalar a c s⁻¹, ?_, ?_⟩, rfl⟩ <;>
    simp [blockScalar, Matrix.fromBlocks_multiply, smul_smul, hs]

theorem block_scaling_identity {a c : ℕ} (D A F : Mat a ℝ)
    (B C : Matrix (Fin a) (Fin c) ℝ) (E : Mat c ℝ) (s : ℝ) (hs : s ≠ 0) :
    blockScalar a c s⁻¹ *
        Matrix.fromBlocks (D + s ^ 2 • F + s • A) (s ^ 2 • C + s • B)
          (s ^ 2 • C + s • B)ᵀ (s ^ 2 • E) * blockScalar a c s⁻¹ =
      Matrix.fromBlocks (D + s • A + s ^ 2 • F) (B + s • C) (B + s • C)ᵀ E := by
  simp only [blockScalar, Matrix.fromBlocks_multiply]
  ext (i | i) (j | j) <;>
    simp [Matrix.fromBlocks, Matrix.transpose_add, Matrix.transpose_smul,
      mul_add, smul_smul] <;>
    field_simp <;> ring

theorem posSemidef_smul_iff {ι : Type u} [Fintype ι] {H : Matrix ι ι ℝ} {s : ℝ}
    (hs : 0 < s) : (s • H).PosSemidef ↔ H.PosSemidef := by
  constructor
  · intro h
    have hh := h.smul (inv_pos.mpr hs).le
    simpa only [smul_smul, inv_mul_cancel₀ hs.ne', one_smul] using hh
  · exact fun h => h.smul hs.le

end Paper256

end

end OAI
