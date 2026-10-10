import OAI.Probability.InvariantIsing.Cavity.CavityCompressionRank
import OAI.Probability.InvariantIsing.Cavity.CavityCompressionBlocks

namespace OAI

/-! The measurable special frame used in the actual base interaction.
Its Gram and cavity-orthogonality identities hold for every input frame. -/

noncomputable section
open MeasureTheory
open scoped Matrix BigOperators

namespace InvariantIsing

lemma cavityCompressionGrams_sum {N n m : ℕ} (g : Fin (N + n) → Fin m)
    (U : Orthogonal (N + n)) : ∑ a, cavityCompressionGrams g U a = 1 := by
  unfold cavityCompressionGrams
  simp_rw [cavitySpectralImage_gram]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, cavitySpectralProjectors_sum, Matrix.mul_one]
  exact cavityColumns_gram U

def cavityConcreteComplement {m n d : ℕ} (e : Fin (m * n) ≃ Fin (d + n))
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ)
    (M : Fin m → Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin (m * n)) (Fin d) ℝ :=
  fun i j => cavitySelectedComplement B₀ (cavityReindexedStack e M) (e i) j

lemma measurable_cavityConcreteComplement {m n d : ℕ}
    (e : Fin (m * n) ≃ Fin (d + n)) (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ) :
    Measurable (cavityConcreteComplement e B₀) := by
  have h := (measurable_cavitySelectedComplement B₀).comp (measurable_cavityReindexedStack e)
  apply Measurable.of_eval_matrix
  intro i j
  exact h.eval_matrix

lemma cavityReindexedStack_compression_gram {N n m d : ℕ}
    (g : Fin (N + n) → Fin m) (e : Fin (m * n) ≃ Fin (d + n))
    (U : Orthogonal (N + n)) :
    (cavityReindexedStack e (cavityCompressionGrams g U)).transpose *
      cavityReindexedStack e (cavityCompressionGrams g U) = 1 := by
  have hM : ∀ a, (cavityCompressionGrams g U a).PosSemidef := by
    intro a
    simpa only [cavityCompressionGrams, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self (cavitySpectralImage g (cavityColumns U) a)
  have hs := cavitySpectralStack_gram (cavityCompressionGrams g U) hM
  rw [cavityCompressionGrams_sum g U] at hs
  ext i j
  change (∑ k : Fin (d + n),
    cavitySpectralStack (cavityCompressionGrams g U) (e.symm k) i *
      cavitySpectralStack (cavityCompressionGrams g U) (e.symm k) j) =
    (1 : Matrix (Fin n) (Fin n) ℝ) i j
  exact (Equiv.sum_comp e.symm (fun k =>
    cavitySpectralStack (cavityCompressionGrams g U) k i *
      cavitySpectralStack (cavityCompressionGrams g U) k j)).trans
        (congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j) hs)

lemma cavityConcreteComplement_gram {N n m d : ℕ}
    (g : Fin (N + n) → Fin m) (e : Fin (m * n) ≃ Fin (d + n))
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ) (U : Orthogonal (N + n)) :
    (cavityConcreteComplement e B₀ (cavityCompressionGrams g U)).transpose *
      cavityConcreteComplement e B₀ (cavityCompressionGrams g U) = 1 := by
  have h := cavitySelectedComplement_gram B₀ _ (cavityReindexedStack_compression_gram g e U)
  ext i j
  change (∑ k : Fin (m * n),
    cavitySelectedComplement B₀ (cavityReindexedStack e (cavityCompressionGrams g U)) (e k) i *
      cavitySelectedComplement B₀ (cavityReindexedStack e (cavityCompressionGrams g U)) (e k) j) = _
  exact (Equiv.sum_comp e (fun k =>
    cavitySelectedComplement B₀ (cavityReindexedStack e (cavityCompressionGrams g U)) k i *
      cavitySelectedComplement B₀ (cavityReindexedStack e (cavityCompressionGrams g U)) k j)).trans
        (congrArg (fun A : Matrix (Fin d) (Fin d) ℝ => A i j) h)

lemma cavityConcreteComplement_perp {N n m d : ℕ}
    (g : Fin (N + n) → Fin m) (e : Fin (m * n) ≃ Fin (d + n))
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ) (U : Orthogonal (N + n)) :
    (cavityConcreteComplement e B₀ (cavityCompressionGrams g U)).transpose *
      cavitySpectralStack (cavityCompressionGrams g U) = 0 := by
  have h := congrArg Matrix.transpose (cavitySelectedComplement_orthogonal B₀ _
    (cavityReindexedStack_compression_gram g e U))
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] at h
  ext i j
  have he := Equiv.sum_comp e (fun k =>
    cavitySelectedComplement B₀ (cavityReindexedStack e (cavityCompressionGrams g U)) k i *
      cavityReindexedStack e (cavityCompressionGrams g U) k j)
  simpa only [cavityConcreteComplement, cavityReindexedStack, Equiv.symm_apply_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply] using
      he.trans (congrArg (fun A : Matrix (Fin d) (Fin n) ℝ => A i j) h)

end InvariantIsing

end

end OAI
