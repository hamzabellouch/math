import OAI.Analysis.Mahler.NormExteriorPower
import Mathlib.LinearAlgebra.Matrix.SchurComplement

namespace OAI

open Complex
open scoped BigOperators

namespace Mahler

def pairSplitEquiv (n : ℕ) : WedgePowerSlots n ≃ Fin n ⊕ Fin n :=
  (pairSlotEquiv n).trans
    { toFun := fun p => if p.2 = 0 then Sum.inl p.1 else Sum.inr p.1
      invFun := Sum.elim (fun i => (i,0)) (fun i => (i,1))
      left_inv := by rintro ⟨i,j⟩; fin_cases j <;> simp
      right_inv := by intro s; cases s <;> simp }

/-- The complex-coordinate coefficient matrix, in split real/imaginary order. -/
noncomputable def hessianCovectorMatrix {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
  Matrix.fromBlocks 1 (I • 1) H ((-I) • H)

lemma hessianCovectorMatrix_det {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) :
    (hessianCovectorMatrix H).det = (-2 * I) ^ n * H.det := by
  rw [hessianCovectorMatrix, Matrix.det_fromBlocks_one₁₁]
  have hm : (-I) • H - H * (I • (1 : Matrix (Fin n) (Fin n) ℂ)) = (-2 * I) • H := by
    simp only [Matrix.mul_smul, Matrix.mul_one]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [hm, Matrix.det_smul, Fintype.card_fin]

noncomputable def splitCoordinates (n : ℕ) : (Fin n ⊕ Fin n) → ComplexEuclidean n →ₗ[ℝ] ℂ :=
  Sum.elim realCoordinate imagCoordinate

lemma pairedCoordinates_split (n : ℕ) : pairedCovectors (coordinatePair (n := n)) =
    splitCoordinates n ∘ pairSplitEquiv n := by
  funext s
  obtain ⟨i,j,h⟩ : ∃ i j, pairSlotEquiv n s = (i,j) := ⟨_,_,rfl⟩
  fin_cases j <;> simp [pairedCovectors, coordinatePair, pairSplitEquiv, splitCoordinates, h]

/-- Coordinate two-form associated with a complex Hessian. This is the
standard (i/2) sum H_ij dz_i wedge dbar(z_j), represented by covectors. -/
noncomputable def hessianPair {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    Fin 2 → ComplexEuclidean n →ₗ[ℝ] ℂ :=
  ![realCoordinate i + I • imagCoordinate i,
    ∑ j, H i j • (realCoordinate j - I • imagCoordinate j)]

noncomputable def matrixTwoForm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) :
    ComplexEuclidean n [⋀^Fin 2]→ₗ[ℝ] ℂ :=
  (I/2) • ∑ i, covectorVolume (hessianPair H i)

lemma hessianPair_split {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) :
    pairedCovectors (hessianPair H) =
      (fun i => ∑ j, hessianCovectorMatrix H i j • splitCoordinates n j) ∘ pairSplitEquiv n := by
  funext s
  obtain ⟨i,j,h⟩ : ∃ i j, pairSlotEquiv n s = (i,j) := ⟨_,_,rfl⟩
  fin_cases j <;>
    simp [pairedCovectors, hessianPair, pairSplitEquiv, hessianCovectorMatrix,
      splitCoordinates, h, Fintype.sum_sum_type, Matrix.one_apply, sub_eq_add_neg,
      Finset.sum_add_distrib, smul_smul, mul_comm]

lemma hessianPair_volume {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) :
    covectorVolume (pairedCovectors (hessianPair H)) =
      ((-2 * I)^n * H.det) • interleavedVolume n := by
  ext v
  rw [hessianPair_split, covectorVolume_reindex_apply, covectorVolume_linearCombination]
  change (hessianCovectorMatrix H).det *
    covectorVolume (splitCoordinates n) (v ∘ (pairSplitEquiv n).symm) = _
  rw [← covectorVolume_reindex_apply, ← pairedCoordinates_split, hessianCovectorMatrix_det]
  rfl

/-- The full n! det(H) normalization, with the i/2 convention and the
positively oriented interleaved real volume form. -/
theorem matrixTwoForm_top {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) :
    wedgePower (matrixTwoForm H) n =
      ((n.factorial : ℂ) * H.det) • interleavedVolume n := by
  rw [matrixTwoForm, wedgePower_smul, wedgePower_sum_pairs_top, hessianPair_volume,
    smul_smul, smul_smul]
  have hc : (I/2) * (-2*I) = 1 := by linear_combination -I_mul_I
  congr 1
  calc
    (I/2)^n * (n.factorial : ℂ) * ((-2*I)^n * H.det) =
        (n.factorial : ℂ) * H.det * ((I/2)*(-2*I))^n := by rw [mul_pow (I/2) (-2*I)]; ac_rfl
    _ = (n.factorial : ℂ) * H.det := by rw [hc, one_pow, mul_one]

noncomputable def matrixPairing {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (w v : ComplexEuclidean n) : ℂ := ∑ i, ∑ j, v i * star (w j) * H i j

lemma hessianPair_zero {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (i : Fin n)
    (v : ComplexEuclidean n) : hessianPair H i 0 v = v i := by
  change ((v i).re : ℂ) + I * ((v i).im : ℂ) = v i
  apply Complex.ext <;> simp

lemma hessianPair_one {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (i : Fin n)
    (v : ComplexEuclidean n) : hessianPair H i 1 v = ∑ j, H i j * star (v j) := by
  change (∑ j, H i j • (realCoordinate j - I • imagCoordinate j)) v = _
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    realCoordinate_apply, imagCoordinate_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  apply Complex.ext <;> simp

lemma matrixTwoForm_apply {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v w : ComplexEuclidean n) :
    matrixTwoForm H ![v,w] = (I/2) * (matrixPairing H w v - matrixPairing H v w) := by
  simp only [matrixTwoForm, AlternatingMap.smul_apply, smul_eq_mul, alternatingMap_sum_apply,
    covectorVolume_apply, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    hessianPair_zero, hessianPair_one, matrixPairing]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end Mahler

end OAI
