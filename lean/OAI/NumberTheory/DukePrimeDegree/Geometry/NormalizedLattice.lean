import OAI.NumberTheory.DukePrimeDegree.Geometry.EmbeddingMatrix
import OAI.NumberTheory.DukePrimeDegree.Geometry.LatticeSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

/-!
# Normalized embedded lattices

Changing the sign of the first basis vector makes an invertible real
basis matrix positively oriented without changing its integer lattice.
Its transpose, scaled by the inverse positive root of its determinant,
then gives a point of the column-lattice homogeneous space.
-/

open Matrix

namespace DukePrimeDegree

variable {n : ℕ} [NeZero n]

/-- Reorient a row basis by changing one sign when necessary. -/
noncomputable def orientBasis (B : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  if 0 < B.det then B else B.updateRow 0 ((-1 : ℝ) • B 0)

lemma det_orientBasis (B : Matrix (Fin n) (Fin n) ℝ) :
    (orientBasis B).det = |B.det| := by
  by_cases h : 0 < B.det
  · simp [orientBasis, h, abs_of_pos h]
  · simp only [orientBasis, h, ↓reduceIte, Matrix.det_updateRow_smul,
      neg_one_mul]
    rw [Matrix.updateRow_eq_self]
    exact (abs_of_nonpos (le_of_not_gt h)).symm

/-- Reorientation preserves the integer span of the rows. -/
lemma span_orientBasis (B : Matrix (Fin n) (Fin n) ℝ) :
    Submodule.span ℤ (Set.range (orientBasis B)) = Submodule.span ℤ (Set.range B) := by
  classical
  by_cases h : 0 < B.det
  · simp [orientBasis, h]
  · simp only [orientBasis, h, ↓reduceIte]
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      by_cases hi : i = 0
      · subst i
        simpa using (Submodule.span ℤ (Set.range B)).neg_mem
          (Submodule.subset_span (Set.mem_range_self 0))
      · rw [Matrix.updateRow_ne hi]
        exact Submodule.subset_span (Set.mem_range_self i)
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      have hm := Submodule.subset_span (R := ℤ)
        (Set.mem_range_self (f := B.updateRow 0 ((-1 : ℝ) • B 0)) i)
      by_cases hi : i = 0
      · subst i
        simpa using (Submodule.span ℤ
          (Set.range (B.updateRow 0 ((-1 : ℝ) • B 0)))).neg_mem hm
      · rwa [Matrix.updateRow_ne hi] at hm

/-- The positive covolume-normalizing scalar. -/
noncomputable def normalizationFactor (B : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (|B.det| ^ ((n : ℝ)⁻¹))⁻¹

omit [NeZero n] in
lemma normalizationFactor_pos (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0) :
    0 < normalizationFactor B := by
  apply inv_pos.mpr
  exact Real.rpow_pos_of_pos (abs_pos.mpr hB) _

lemma det_normalizedBasis (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0) :
    (normalizationFactor B • (orientBasis B)ᵀ).det = 1 := by
  rw [Matrix.det_smul, Fintype.card_fin, Matrix.det_transpose, det_orientBasis]
  unfold normalizationFactor
  rw [inv_pow, Real.rpow_inv_natCast_pow (abs_nonneg _) (NeZero.ne n)]
  exact inv_mul_cancel₀ (abs_ne_zero.mpr hB)

/-- The special-linear matrix of the normalized column lattice. -/
noncomputable def normalizedBasis (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0) :
    RealSL n := ⟨normalizationFactor B • (orientBasis B)ᵀ, det_normalizedBasis B hB⟩

/-- An invertible row basis determines a covolume-one lattice. -/
noncomputable def latticePoint (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0) :
    LatticeSpace n := QuotientGroup.mk (normalizedBasis B hB)

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]

/-- The ordered real embedding, regarded as an integer-linear map. -/
noncomputable def realEmbeddingLinear (σ : EmbeddingOrder K n) :
    K →ₗ[ℤ] (Fin n → ℝ) :=
  LinearMap.pi fun j => (orderedRealEmbedding σ j).toAddMonoidHom.toIntLinearMap

lemma FullLattice.span_embeddingMatrix (M : FullLattice K)
    (σ : EmbeddingOrder K (Module.finrank ℚ K)) :
    Submodule.span ℤ (Set.range
      (realEmbeddingMatrix (fun i => (M.integralBasis i : K)) σ)) =
      M.toSubmodule.map (realEmbeddingLinear σ) := by
  have hspan : Submodule.span ℤ
      (Set.range fun i => (M.integralBasis i : K)) = M.toSubmodule := by
    rw [show (Set.range fun i => (M.integralBasis i : K)) =
      M.toSubmodule.subtype '' Set.range M.integralBasis by ext; simp]
    rw [← Submodule.map_span, M.integralBasis.span_eq]
    simp
  have hrange : Set.range
      (realEmbeddingMatrix (fun i => (M.integralBasis i : K)) σ) =
      (realEmbeddingLinear σ) '' (Set.range fun i => (M.integralBasis i : K)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  rw [hrange, ← Submodule.map_span, hspan]

/-- The normalized embedded lattice attached to a full lattice and an
ordering of the real embeddings. -/
noncomputable def FullLattice.point (M : FullLattice K)
    (σ : EmbeddingOrder K (Module.finrank ℚ K)) :
    LatticeSpace (Module.finrank ℚ K) := by
  let : NeZero (Module.finrank ℚ K) := ⟨ne_of_gt Module.finrank_pos⟩
  exact latticePoint (realEmbeddingMatrix (fun i => (M.integralBasis i : K)) σ)
    (M.det_embeddingMatrix_ne_zero σ)

end DukePrimeDegree

end OAI
