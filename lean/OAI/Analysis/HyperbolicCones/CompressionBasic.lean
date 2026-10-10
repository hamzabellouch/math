import OAI.Analysis.HyperbolicCones.MatrixLinear

namespace OAI

noncomputable section

open Matrix

universe u v

namespace Paper256

theorem posSemidef_fromBlocks_diagonal_iff {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ) :
    (Matrix.fromBlocks A 0 0 B).PosSemidef ↔ A.PosSemidef ∧ B.PosSemidef := by
  constructor
  · intro h
    constructor
    · convert h.submatrix Sum.inl using 1
      ext i j
      rfl
    · convert h.submatrix Sum.inr using 1
      ext i j
      rfl
  · rintro ⟨hA, hB⟩
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (Matrix.IsHermitian.fromBlocks hA.isHermitian (by simp) hB.isHermitian)
    intro v
    have ha := hA.dotProduct_mulVec_nonneg (v ∘ Sum.inl)
    have hb := hB.dotProduct_mulVec_nonneg (v ∘ Sum.inr)
    simpa [Matrix.fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type] using add_nonneg ha hb

theorem matrix_compression_posSemidef_iff {ι : Type u} [Fintype ι]
    (p : ι → Prop) [DecidablePred p] (M : Matrix ι ι ℝ) (hM : M.IsHermitian)
    (hzero : ∀ i, ¬p i → ∀ j, M i j = 0) :
    M.PosSemidef ↔ (M.submatrix (Subtype.val : {i // p i} → ι) Subtype.val).PosSemidef := by
  let e := Equiv.sumCompl p
  have heq : M.submatrix e e = Matrix.fromBlocks
      (M.submatrix (Subtype.val : {i // p i} → ι) Subtype.val) 0 0 0 := by
    ext (i | i) (j | j)
    · rfl
    · change M i.val j.val = 0
      have hs : M i.val j.val = M j.val i.val := by simpa using hM.apply j.val i.val
      rw [hs, hzero j.val j.property]
    · exact hzero i.val i.property j.val
    · exact hzero i.val i.property j.val
  calc
    M.PosSemidef ↔ (M.submatrix e e).PosSemidef := (Matrix.posSemidef_submatrix_equiv e).symm
    _ ↔ (M.submatrix (Subtype.val : {i // p i} → ι) Subtype.val).PosSemidef := by
      rw [heq, posSemidef_fromBlocks_diagonal_iff]
      simp only [Matrix.PosSemidef.zero, and_true]

end Paper256

end

end OAI
