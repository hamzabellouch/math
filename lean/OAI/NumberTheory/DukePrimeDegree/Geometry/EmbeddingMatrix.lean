import OAI.NumberTheory.DukePrimeDegree.Arithmetic.LatticeBasis
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.Discriminant

namespace OAI

/-!
# Ordered real embeddings and lattice basis matrices

An ordering of the complex embeddings of a totally real field gives the
ordered real embeddings used in the manuscript. The matrix of any full
lattice basis under these embeddings has nonzero determinant.
-/

namespace DukePrimeDegree

variable {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K]
  {n : ℕ}

/-- An ordering of all embeddings; total reality makes their values real. -/
abbrev EmbeddingOrder (K : Type*) [Field K] [NumberField K] (n : ℕ) :=
  Fin n ≃ (K →ₐ[ℚ] ℂ)

/-- The real ring embedding at one place of the ordering. -/
noncomputable def orderedRealEmbedding (σ : EmbeddingOrder K n) (j : Fin n) : K →+* ℝ :=
  (NumberField.IsTotallyReal.complexEmbedding_isReal (σ j).toRingHom).embedding

@[simp] lemma orderedRealEmbedding_complex (σ : EmbeddingOrder K n)
    (j : Fin n) (x : K) : (orderedRealEmbedding σ j x : ℂ) = σ j x :=
  NumberField.ComplexEmbedding.IsReal.coe_embedding_apply _ _

/-- Rows are basis vectors and columns are ordered real embeddings. -/
noncomputable def realEmbeddingMatrix (b : Fin n → K) (σ : EmbeddingOrder K n) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => orderedRealEmbedding σ j (b i)

lemma realEmbeddingMatrix_complex (b : Fin n → K) (σ : EmbeddingOrder K n) :
    (realEmbeddingMatrix b σ).map Complex.ofRealHom =
      Algebra.embeddingsMatrixReindex ℚ ℂ b σ := by
  ext i j
  simp [realEmbeddingMatrix, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix]

/-- The field trace discriminant proves the embedded lattice basis is
linearly independent over the real numbers. -/
theorem det_realEmbeddingMatrix_ne_zero (b : Module.Basis (Fin n) ℚ K)
    (σ : EmbeddingOrder K n) : (realEmbeddingMatrix b σ).det ≠ 0 := by
  have hdisc : (algebraMap ℚ ℂ) (Algebra.discr ℚ b) ≠ 0 := by
    intro h
    apply Algebra.discr_not_zero_of_basis ℚ b
    apply (algebraMap ℚ ℂ).injective
    simpa only [map_zero] using h
  have heq := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ b σ
  have hdet : (Algebra.embeddingsMatrixReindex ℚ ℂ b σ).det ≠ 0 := by
    intro h
    apply hdisc
    rw [heq, h, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  intro hreal
  apply hdet
  rw [← realEmbeddingMatrix_complex]
  change (Complex.ofRealHom.mapMatrix (realEmbeddingMatrix b σ)).det = 0
  rw [← RingHom.map_det, hreal, map_zero]

/-- In particular this applies to the chosen integer basis of a full lattice. -/
theorem FullLattice.det_embeddingMatrix_ne_zero (M : FullLattice K)
    (σ : EmbeddingOrder K (Module.finrank ℚ K)) :
    (realEmbeddingMatrix (fun i => (M.integralBasis i : K)) σ).det ≠ 0 := by
  have h := det_realEmbeddingMatrix_ne_zero (M.rationalBasis M.integralBasis) σ
  have hb : (M.rationalBasis M.integralBasis : Fin (Module.finrank ℚ K) → K) =
      fun i => (M.integralBasis i : K) := by
    funext i
    exact M.rationalBasis_apply M.integralBasis i
  rwa [hb] at h

end DukePrimeDegree

end OAI
