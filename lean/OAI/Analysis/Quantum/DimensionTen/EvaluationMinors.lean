import OAI.Analysis.Quantum.DimensionTen.AlphaMinors
import OAI.Analysis.Quantum.DimensionTen.GaloisField
import OAI.Analysis.Quantum.DimensionTen.IndependentMinor

namespace OAI

section
noncomputable section
open Polynomial Matrix
namespace DimensionTen.Border

def evaluationMatrix : Matrix (Fin 20) (Fin 20) K :=
  fun i j => embeddingsK j (low alpha i)

lemma evaluationMatrix_map : evaluationMatrix.map complexEmbedding =
    Algebra.embeddingsMatrixReindex ℚ ℂ basis embeddingsC := by
  ext i j
  change complexEmbedding (embeddingsK j (low alpha i)) = embeddingsC j (basis i)
  rw [basis_eq]
  rfl

lemma evaluationMatrix_det_ne : evaluationMatrix.det ≠ 0 := by
  intro hz
  have hd := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ basis embeddingsC
  have hc : (Algebra.embeddingsMatrixReindex ℚ ℂ basis embeddingsC).det = 0 := by
    rw [← evaluationMatrix_map]
    erw [← complexEmbedding.map_det, hz, map_zero]
  rw [hc, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hd
  exact Algebra.discr_not_zero_of_basis ℚ basis ((algebraMap ℚ ℂ).injective (hd.trans (map_zero _).symm))

abbrev firstTen : Fin 10 → Fin 20 := Fin.castLE (by decide)

lemma some_ten_minor : ∃ a : Fin 10 → Fin 20, Function.Injective a ∧
    (evaluationMatrix.submatrix firstTen a).det ≠ 0 := by
  obtain ⟨a, ha, hd⟩ := Arithmetic.independent_minor
    (evaluationMatrix.submatrix firstTen id)
    (Arithmetic.restrict_rows_surjective evaluationMatrix evaluationMatrix_det_ne
      firstTen (Fin.castLE_injective _))
  exact ⟨a, ha, hd⟩

lemma every_ten_minor (b : Fin 10 → Fin 20) (hb : Function.Injective b) :
    (evaluationMatrix.submatrix firstTen b).det ≠ 0 := by
  classical
  obtain ⟨a, ha, hd⟩ := some_ten_minor
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_extending_pair a b ha hb
  obtain ⟨σ, hσ⟩ := galois_permute π
  have he : (evaluationMatrix.submatrix firstTen a).map σ.toRingHom =
      evaluationMatrix.submatrix firstTen b := by
    ext i j
    change σ (embeddingsK (a j) (low alpha (firstTen i))) =
      embeddingsK (b j) (low alpha (firstTen i))
    have hh := congrArg (fun τ : L →ₐ[ℚ] K => τ (low alpha (firstTen i))) (hσ (a j))
    rw [hπ] at hh
    exact hh
  rw [← he]
  erw [← σ.map_det]
  exact (map_ne_zero σ.toRingHom).mpr hd

def points (i : Fin 20) : Fin 3 → ℂ := fun j => embeddingsC i (alpha j)

lemma ten_complex_minor (b : Fin 10 → Fin 20) (hb : Function.Injective b) :
    Matrix.det (fun i j : Fin 10 => low (points (b j)) (firstTen i)) ≠ 0 := by
  have he : (evaluationMatrix.submatrix firstTen b).map complexEmbedding =
      (fun i j : Fin 10 => low (points (b j)) (firstTen i)) := by
    ext i j
    change embeddingsC (b j) (low alpha (firstTen i)) = _
    exact low_map (embeddingsC (b j)).toRingHom alpha (firstTen i)
  rw [← he]
  erw [← complexEmbedding.map_det]
  exact (map_ne_zero complexEmbedding).mpr (every_ten_minor b hb)

end DimensionTen.Border

end
end

end OAI
