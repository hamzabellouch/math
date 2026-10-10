import OAI.Probability.InvariantIsing.Haar.SpecialPlaneRotation
import OAI.Probability.InvariantIsing.Spectral.SpectralCountComparison

namespace OAI

/-! Spectral reorderings can be realized inside SO(N). A single row sign
corrects a permutation determinant without changing any squared projection. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Matrix

namespace InvariantIsing

lemma permutationMatrix_orthogonal {N : ℕ} (p : Equiv.Perm (Fin N)) :
    p.permMatrix ℝ ∈ Matrix.orthogonalGroup (Fin N) ℝ := by
  apply (Matrix.mem_orthogonalGroup_iff (Fin N) ℝ).mpr
  rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul]
  simp

lemma permutationMatrix_det_sq {N : ℕ} (p : Equiv.Perm (Fin N)) :
    (p.permMatrix ℝ).det ^ 2 = 1 := by
  let U : Orthogonal N := ⟨p.permMatrix ℝ, permutationMatrix_orthogonal p⟩
  rcases orthogonal_det_eq_one_or_neg_one U with h | h <;>
    change (p.permMatrix ℝ).det = _ at h <;> rw [h] <;> norm_num

def permutationSignDiagonal {N : ℕ} (hN : 0 < N) (p : Equiv.Perm (Fin N)) :
    Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal fun i => if i = (⟨0, hN⟩ : Fin N) then (p.permMatrix ℝ).det else 1

lemma permutationSignDiagonal_sq {N : ℕ} (hN : 0 < N) (p : Equiv.Perm (Fin N)) :
    permutationSignDiagonal hN p * (permutationSignDiagonal hN p)ᵀ = 1 := by
  rw [permutationSignDiagonal, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    split_ifs
    · exact (pow_two ((p.permMatrix ℝ).det)).symm.trans (permutationMatrix_det_sq p)
    · norm_num
  · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

lemma permutationSignDiagonal_det {N : ℕ} (hN : 0 < N) (p : Equiv.Perm (Fin N)) :
    (permutationSignDiagonal hN p).det = (p.permMatrix ℝ).det := by
  simp [permutationSignDiagonal, Matrix.det_diagonal]

/-- A permutation of spectral coordinates, with determinant corrected to one. -/
def spectralPermutation {N : ℕ} (hN : 0 < N) (p : Equiv.Perm (Fin N)) :
    SpecialOrthogonal N :=
  ⟨permutationSignDiagonal hN p * p.permMatrix ℝ, by
    apply Matrix.mem_specialOrthogonalGroup_iff.mpr
    constructor
    · apply (Matrix.mem_orthogonalGroup_iff (Fin N) ℝ).mpr
      rw [Matrix.transpose_mul]
      calc
        _ = permutationSignDiagonal hN p *
            (p.permMatrix ℝ * (p.permMatrix ℝ)ᵀ) * (permutationSignDiagonal hN p)ᵀ := by
          simp only [Matrix.mul_assoc]
        _ = permutationSignDiagonal hN p * (permutationSignDiagonal hN p)ᵀ := by
          rw [(Matrix.mem_orthogonalGroup_iff (Fin N) ℝ).mp (permutationMatrix_orthogonal p)]
          simp
        _ = 1 := permutationSignDiagonal_sq hN p
    · rw [Matrix.det_mul, permutationSignDiagonal_det, ← pow_two, permutationMatrix_det_sq]⟩

lemma spectralPermutation_coordinate_sq {N : ℕ} (hN : 0 < N)
    (p : Equiv.Perm (Fin N)) (U : SpecialOrthogonal N)
    (x : EuclideanSpace ℝ (Fin N)) (i : Fin N) :
    (specialRotation (spectralPermutation hN p * U) x i) ^ 2 =
      (specialRotation U x (p i)) ^ 2 := by
  have he : specialRotation (spectralPermutation hN p * U) x i =
      (if i = (⟨0, hN⟩ : Fin N) then (p.permMatrix ℝ).det else 1) *
        specialRotation U x (p i) := by
    change (((permutationSignDiagonal hN p * p.permMatrix ℝ) *
      (U : Matrix (Fin N) (Fin N) ℝ)) *ᵥ x.ofLp) i = _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.permMatrix_mulVec]
    simp only [permutationSignDiagonal, Matrix.mulVec_diagonal,
      Function.comp_apply, specialRotation_apply]
    rfl
  rw [he, mul_pow]
  split_ifs
  · rw [permutationMatrix_det_sq, one_mul]
  · rw [one_pow, one_mul]

lemma rotatedEnergy_spectralPermutation {N : ℕ} (hN : 0 < N)
    (p : Equiv.Perm (Fin N)) (eig : Fin N → ℝ) (U : SpecialOrthogonal N) (σ : Spin N) :
    rotatedEnergy (fun i => eig (p i)) (specialRotation (spectralPermutation hN p * U)) σ =
      rotatedEnergy eig (specialRotation U) σ := by
  simp only [rotatedEnergy, spectralPermutation_coordinate_sq]
  rw [Equiv.sum_comp p (fun i => eig i * (specialRotation U (spinVector σ) i) ^ 2)]

lemma meanPressure_spectralPermutation {N : ℕ} (hN : 0 < N)
    (μ : Measure (SpecialOrthogonal N)) [μ.IsMulLeftInvariant]
    (p : Equiv.Perm (Fin N)) (eig c : Fin N → ℝ) :
    (∫ U, rotatedPressure (fun i => eig (p i)) (specialRotation U) c ∂μ) =
      ∫ U, rotatedPressure eig (specialRotation U) c ∂μ := by
  have he (U : SpecialOrthogonal N) :
      rotatedPressure (fun i => eig (p i)) (specialRotation (spectralPermutation hN p * U)) c =
        rotatedPressure eig (specialRotation U) c := by
    simp only [rotatedPressure, rotatedEnergy_spectralPermutation]
  rw [← integral_mul_left_eq_self
    (fun U => rotatedPressure (fun i => eig (p i)) (specialRotation U) c)
    (spectralPermutation hN p)]
  simp only [he]

end InvariantIsing

end

end OAI
