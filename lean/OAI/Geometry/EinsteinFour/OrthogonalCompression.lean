import OAI.Geometry.EinsteinFour.DeterminantCompression
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace OAI

/-! Determinant compression after an orthogonal change of basis. -/

namespace PositiveEinsteinFour.Jacobi

open Matrix

noncomputable section

/-- Complete orthonormal columns to an orthogonal matrix while keeping
each prescribed column in its original position. -/
theorem orthogonal_extension {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (W : Matrix (m ⊕ n) m ℝ) (hW : Wᴴ * W = 1) :
    ∃ U : Matrix (m ⊕ n) (m ⊕ n) ℝ,
      U * Uᴴ = 1 ∧ ∀ i j, U i (Sum.inl j) = W i j := by
  let v : m ⊕ n → EuclideanSpace ℝ (m ⊕ n) :=
    Sum.elim (fun j => WithLp.toLp 2 (fun i => W i j)) (fun _ => 0)
  have hw : Orthonormal ℝ (fun j : m => v (Sum.inl j)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have h := congrFun (congrFun hW i) j
    simpa [v, Matrix.mul_apply, Matrix.conjTranspose_apply, PiLp.inner_apply,
      RCLike.inner_apply, Matrix.one_apply, mul_comm] using h
  let s : Set (m ⊕ n) := Set.range Sum.inl
  have hs : Orthonormal ℝ (s.domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, a, rfl⟩ ⟨j, b, rfl⟩
    simpa only [Set.domRestrict_apply, Subtype.ext_iff, Sum.inl.injEq] using
      (orthonormal_iff_ite.mp hw a b)
  obtain ⟨b, hb⟩ := hs.exists_orthonormalBasis_extension_of_card_eq
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (m ⊕ n)) = Fintype.card (m ⊕ n))
  let a := EuclideanSpace.basisFun (m ⊕ n) ℝ
  refine ⟨a.toBasis.toMatrix b, a.toMatrix_orthonormalBasis_self_mul_conjTranspose b, ?_⟩
  intro i j
  change a.repr (b (Sum.inl j)) i = W i j
  rw [hb (Sum.inl j) ⟨j, rfl⟩]
  rfl

theorem trace_sum_blocks {m n : Type*} [Fintype m] [Fintype n]
    (B : Matrix (m ⊕ n) (m ⊕ n) ℝ) :
    B.trace = B.toBlocks₁₁.trace + B.toBlocks₂₂.trace := by
  simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type,
    Matrix.toBlocks₁₁, Matrix.toBlocks₂₂]

/-- The determinant loss depends on the first compression and total trace,
not on the choice of an orthonormal basis of its complement. -/
theorem det_le_orthogonal_compression {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {A U : Matrix (m ⊕ n) (m ⊕ n) ℝ}
    (hA : A.PosDef) (hU : U * Uᴴ = 1)
    (htrace : A.trace ≤ Fintype.card m + Fintype.card n)
    (hfirst : (Uᴴ * A * U).toBlocks₁₁.trace = Fintype.card m) :
    A.det ≤ (Uᴴ * A * U).toBlocks₁₁.det := by
  have hdetU : U.det * Uᴴ.det = 1 := by
    rw [← Matrix.det_mul, hU, Matrix.det_one]
  have hunit : IsUnit U := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    apply isUnit_iff_ne_zero.mpr
    intro hz
    rw [hz, zero_mul] at hdetU
    exact zero_ne_one hdetU
  let B := Uᴴ * A * U
  have hB : B.PosDef := hA.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_of_isUnit hunit)
  have htrB : B.trace = A.trace := by
    dsimp [B]
    rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]
  have hdetB : B.det = A.det := by
    dsimp [B]
    rw [Matrix.det_mul, Matrix.det_mul]
    calc
      Uᴴ.det * A.det * U.det = A.det * (U.det * Uᴴ.det) := by ring
      _ = A.det := by rw [hdetU, mul_one]
  have hcross : B.toBlocks₂₁ = B.toBlocks₁₂ᴴ := by
    ext i j
    exact congrFun (congrFun hB.isHermitian.eq (Sum.inl j)) (Sum.inr i)
  have hblocks : fromBlocks B.toBlocks₁₁ B.toBlocks₁₂ B.toBlocks₁₂ᴴ B.toBlocks₂₂ = B := by
    rw [← hcross, Matrix.fromBlocks_toBlocks]
  have hcomplement : B.toBlocks₂₂.trace ≤ Fintype.card n := by
    have ht := trace_sum_blocks B
    change B.toBlocks₁₁.trace = _ at hfirst
    linarith
  have hbound := det_posDef_fromBlocks_le_first
    (hblocks.symm ▸ hB) hcomplement
  rwa [hblocks, hdetB] at hbound

/-- An orthonormal family of columns is enough to apply the determinant
comparison; the complementary basis is constructed, not assumed. -/
theorem det_le_isometric_compression {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {A : Matrix (m ⊕ n) (m ⊕ n) ℝ} (W : Matrix (m ⊕ n) m ℝ)
    (hA : A.PosDef) (hW : Wᴴ * W = 1)
    (htrace : A.trace ≤ Fintype.card m + Fintype.card n)
    (hfirst : (Wᴴ * A * W).trace = Fintype.card m) :
    A.det ≤ (Wᴴ * A * W).det := by
  obtain ⟨U, hU, hUW⟩ := orthogonal_extension W hW
  have heq : (Uᴴ * A * U).toBlocks₁₁ = Wᴴ * A * W := by
    ext i j
    simp [Matrix.toBlocks₁₁, Matrix.mul_apply, hUW]
  have h := det_le_orthogonal_compression hA hU htrace (heq ▸ hfirst)
  rwa [heq] at h

/-- Reindexing version for a matrix whose ambient coordinates need not
already separate the distinguished columns from their complement. -/
theorem det_le_isometric_compression_of_card {I m n : Type*}
    [Fintype I] [Fintype m] [Fintype n]
    [DecidableEq I] [DecidableEq m] [DecidableEq n]
    (hcard : Fintype.card I = Fintype.card m + Fintype.card n)
    {A : Matrix I I ℝ} (W : Matrix I m ℝ)
    (hA : A.PosDef) (hW : Wᴴ * W = 1)
    (htrace : A.trace ≤ Fintype.card I)
    (hfirst : (Wᴴ * A * W).trace = Fintype.card m) :
    A.det ≤ (Wᴴ * A * W).det := by
  let e : m ⊕ n ≃ I := Fintype.equivOfCardEq (by simpa using hcard.symm)
  let A' := A.submatrix e e
  let W' := W.submatrix e id
  have hgram : W'ᴴ * W' = Wᴴ * W := by
    simp only [W', Matrix.conjTranspose_submatrix]
    exact Matrix.submatrix_mul_equiv Wᴴ W id e id
  have hcompression : W'ᴴ * A' * W' = Wᴴ * A * W := by
    simp only [W', A', Matrix.conjTranspose_submatrix]
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    rfl
  have htr : A'.trace = A.trace := by
    exact e.sum_comp (fun i => A i i)
  have h := det_le_isometric_compression W' (hA.submatrix e.injective)
    (hgram.trans hW) (by rw [htr]; simpa [hcard] using htrace)
    (by rw [hcompression]; exact hfirst)
  simpa only [A', Matrix.det_submatrix_equiv_self, hcompression] using h

end

end PositiveEinsteinFour.Jacobi

end OAI
