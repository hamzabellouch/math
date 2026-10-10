import OAI.Analysis.Pureness.Cuntz.MatrixDiagonal
import Mathlib.Data.Matrix.Basis

namespace OAI
namespace CuntzPureness
open scoped ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def TracialState.comap (ρ : TracialState B) (φ : A →⋆ₐ[ℂ] B) : TracialState A where
  functional :=
    { ρ.functional.toLinearMap.comp φ.toLinearMap with
      monotone' := by
        intro a b hab
        change ρ.functional (φ a) ≤ ρ.functional (φ b)
        apply ρ.functional.monotone
        apply sub_nonneg.mp
        rw [← map_sub]
        exact starAlgHom_positive φ (b - a) (sub_nonneg.mpr hab) }
  normalized := by change ρ.functional (φ 1) = 1; rw [map_one, ρ.normalized]
  tracial a b := by
    change ρ.functional (φ (a * b)) = ρ.functional (φ (b * a))
    rw [map_mul φ, map_mul φ, ρ.tracial]

noncomputable def scalarMatrixHom : A →⋆ₐ[ℂ] CStarMatrix ι ι A where
  toFun a := diagonalMatrixHom (fun _ : ι => a)
  map_one' := diagonalMatrixHom.map_one
  map_zero' := diagonalMatrixHom.map_zero
  map_add' a b := diagonalMatrixHom.map_add (fun _ => a) (fun _ => b)
  map_mul' a b := diagonalMatrixHom.map_mul (fun _ => a) (fun _ => b)
  commutes' z := diagonalMatrixHom.commutes z
  map_star' a := map_star diagonalMatrixHom (fun _ => a)

noncomputable def singleMatrix (i j : ι) (a : A) : CStarMatrix ι ι A :=
  CStarMatrix.ofMatrix (Matrix.single i j a)

omit [PartialOrder A] [StarOrderedRing A] in
lemma singleMatrix_mul_same (i j k : ι) (a b : A) :
    singleMatrix i j a * singleMatrix j k b = singleMatrix i k (a * b) := by
  change CStarMatrix.ofMatrixStarAlgEquiv (Matrix.single i j a) *
    CStarMatrix.ofMatrixStarAlgEquiv (Matrix.single j k b) =
      CStarMatrix.ofMatrixStarAlgEquiv (Matrix.single i k (a * b))
  rw [← map_mul, Matrix.single_mul_single_same]

omit [PartialOrder A] [StarOrderedRing A] in
lemma singleMatrix_mul_ne (i j k l : ι) (hjk : j ≠ k) (a b : A) :
    singleMatrix i j a * singleMatrix k l b = 0 := by
  change CStarMatrix.ofMatrixStarAlgEquiv (Matrix.single i j a) *
    CStarMatrix.ofMatrixStarAlgEquiv (Matrix.single k l b) = _
  rw [← map_mul]
  have hzero : Matrix.single i j a * Matrix.single k l b = 0 := by
    exact Matrix.single_mul_single_of_ne a i j k hjk b
  rw [hzero, map_zero]

omit [PartialOrder A] [StarOrderedRing A] in
lemma matrix_eq_sum_single (M : CStarMatrix ι ι A) :
    M = ∑ i, ∑ j, singleMatrix i j (M i j) := by
  have heq := congrArg CStarMatrix.ofMatrixStarAlgEquiv
    (Matrix.matrix_eq_sum_single (CStarMatrix.ofMatrix.symm M))
  simp only [map_sum] at heq
  convert heq using 1 <;> rfl

lemma trace_single_offDiagonal (ρ : TracialState (CStarMatrix ι ι A))
    (i j : ι) (hij : i ≠ j) (a : A) : ρ.functional (singleMatrix i j a) = 0 := by
  have ht := ρ.tracial (singleMatrix i i 1) (singleMatrix i j a)
  rw [singleMatrix_mul_same, one_mul, singleMatrix_mul_ne i j i i hij.symm,
    map_zero] at ht
  exact ht

lemma trace_single_diagonal_eq (ρ : TracialState (CStarMatrix ι ι A))
    (i j : ι) (a : A) : ρ.functional (singleMatrix i i a) = ρ.functional (singleMatrix j j a) := by
  have ht := ρ.tracial (singleMatrix i j a) (singleMatrix j i 1)
  simpa only [singleMatrix_mul_same, mul_one, one_mul] using ht

lemma trace_matrix_eq_sum_diagonal (ρ : TracialState (CStarMatrix ι ι A))
    (M : CStarMatrix ι ι A) :
    ρ.functional M = ∑ i, ρ.functional (singleMatrix i i (M i i)) := by
  nth_rw 1 [matrix_eq_sum_single M]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum]
  apply Finset.sum_eq_single i
  · intro j _ hji
    exact trace_single_offDiagonal ρ i j hji.symm (M i j)
  · simp

omit [PartialOrder A] [StarOrderedRing A] in
lemma scalarMatrix_eq_sum_single (a : A) :
    (scalarMatrixHom a : CStarMatrix ι ι A) = ∑ i, singleMatrix i i a := by
  have heq := congrArg CStarMatrix.ofMatrixStarAlgEquiv
    (Matrix.sum_single_eq_diagonal (fun _ : ι => a)).symm
  simp only [map_sum] at heq
  convert heq using 1 <;> rfl

lemma trace_scalarMatrix (ρ : TracialState (CStarMatrix ι ι A)) (a : A) (i : ι) :
    ρ.functional (scalarMatrixHom a) =
      (Fintype.card ι : ℂ) * ρ.functional (singleMatrix i i a) := by
  rw [scalarMatrix_eq_sum_single, map_sum]
  simp_rw [trace_single_diagonal_eq ρ _ i a]
  simp

theorem matrixTrace_comap_scale (ρ : TracialState (CStarMatrix ι ι A))
    (M : CStarMatrix ι ι A) :
    matrixTrace (ρ.comap scalarMatrixHom) M = (Fintype.card ι : ℂ) * ρ.functional M := by
  change (∑ i, ρ.functional (scalarMatrixHom (M i i))) = _
  calc
    _ = ∑ i, (Fintype.card ι : ℂ) * ρ.functional (singleMatrix i i (M i i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact trace_scalarMatrix ρ (M i i) i
    _ = _ := by rw [← Finset.mul_sum, ← trace_matrix_eq_sum_diagonal]

omit [StarOrderedRing A] in
@[ext] lemma TracialState.ext {τ ρ : TracialState A}
    (h : ∀ a, τ.functional a = ρ.functional a) : τ = ρ := by
  have heq : τ.functional = ρ.functional := PositiveLinearMap.ext h
  cases τ
  cases ρ
  congr

theorem matrixTracialState_comap [Nonempty ι] (ρ : TracialState (CStarMatrix ι ι A)) :
    matrixTracialState (ρ.comap scalarMatrixHom) = ρ := by
  apply TracialState.ext
  intro M
  change (Fintype.card ι : ℂ)⁻¹ * matrixTrace (ρ.comap scalarMatrixHom) M = ρ.functional M
  rw [matrixTrace_comap_scale, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]

theorem comap_matrixTracialState [Nonempty ι] (τ : TracialState A) :
    (matrixTracialState (ι := ι) τ).comap scalarMatrixHom = τ := by
  apply TracialState.ext
  intro a
  change (Fintype.card ι : ℂ)⁻¹ * matrixTrace τ (scalarMatrixHom a) = τ.functional a
  have heq : matrixTrace τ (scalarMatrixHom a : CStarMatrix ι ι A) =
      (Fintype.card ι : ℂ) * τ.functional a := by
    change (∑ i : ι, τ.functional (diagonalMatrixHom (fun _ : ι => a) i i)) = _
    simp [diagonalMatrixHom_apply]
  rw [heq, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]

theorem matrix_tracialState_nonempty_iff [Nonempty ι] :
    Nonempty (TracialState (CStarMatrix ι ι A)) ↔ Nonempty (TracialState A) := by
  constructor
  · rintro ⟨ρ⟩
    exact ⟨ρ.comap scalarMatrixHom⟩
  · rintro ⟨τ⟩
    exact ⟨matrixTracialState τ⟩
end CuntzPureness

end OAI
