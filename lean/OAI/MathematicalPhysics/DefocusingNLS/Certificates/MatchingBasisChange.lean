import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralMatchingAnalytic
import Mathlib.Analysis.Analytic.Order

namespace OAI

/-! Separate changes of regular and outgoing bases preserve the matching
zeros; invertible holomorphic changes also preserve their multiplicities. -/

namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)
local notation "J₄" => Fin 2 × Fin 2

noncomputable def matchingBasisChange (A B : Matrix (Fin 2) (Fin 2) ℂ) : Matrix J₄ J₄ ℂ :=
  (Matrix.blockDiagonal ![A,B]).submatrix (Equiv.prodComm _ _) (Equiv.prodComm _ _)

theorem matchingBasisChange_det (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    (matchingBasisChange A B).det=A.det*B.det := by
  rw [matchingBasisChange,Matrix.det_submatrix_equiv_self (Equiv.prodComm _ _),
    Matrix.det_blockDiagonal,Fin.prod_univ_two]
  rfl

theorem spectralMatchingMatrix_change (R₀ R₁ O₀ O₁ : E₄)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    spectralMatchingMatrix (A 0 0 • R₀+A 1 0 • R₁) (A 0 1 • R₀+A 1 1 • R₁)
      (B 0 0 • O₀+B 1 0 • O₁) (B 0 1 • O₀+B 1 1 • O₁)=
    spectralMatchingMatrix R₀ R₁ O₀ O₁*matchingBasisChange A B := by
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [spectralMatchingMatrix,spectralStateCoordinates,spectralMatchingColumns,
      matchingBasisChange,Matrix.blockDiagonal,Matrix.submatrix,Matrix.mul_apply,
      Fintype.sum_prod_type,Fin.sum_univ_two,smul_eq_mul] <;> ring

theorem spectralMatchingDeterminant_change (R₀ R₁ O₀ O₁ : E₄)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    spectralMatchingDeterminant (A 0 0 • R₀+A 1 0 • R₁) (A 0 1 • R₀+A 1 1 • R₁)
      (B 0 0 • O₀+B 1 0 • O₁) (B 0 1 • O₀+B 1 1 • O₁)=
    (A.det*B.det)*spectralMatchingDeterminant R₀ R₁ O₀ O₁ := by
  unfold spectralMatchingDeterminant
  rw [spectralMatchingMatrix_change,Matrix.det_mul,matchingBasisChange_det]
  ring

theorem spectralMatchingDeterminant_change_order
    (R₀ R₁ O₀ O₁ : ℂ → E₄) (A B : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ)
    (hR₀ : AnalyticAt ℂ R₀ z) (hR₁ : AnalyticAt ℂ R₁ z)
    (hO₀ : AnalyticAt ℂ O₀ z) (hO₁ : AnalyticAt ℂ O₁ z)
    (hA : ∀ i j, AnalyticAt ℂ (fun w => A w i j) z)
    (hB : ∀ i j, AnalyticAt ℂ (fun w => B w i j) z)
    (hAz : (A z).det≠0) (hBz : (B z).det≠0) :
    analyticOrderAt (fun w => spectralMatchingDeterminant
      (A w 0 0 • R₀ w+A w 1 0 • R₁ w) (A w 0 1 • R₀ w+A w 1 1 • R₁ w)
      (B w 0 0 • O₀ w+B w 1 0 • O₁ w) (B w 0 1 • O₀ w+B w 1 1 • O₁ w)) z=
    analyticOrderAt (fun w => spectralMatchingDeterminant (R₀ w) (R₁ w) (O₀ w) (O₁ w)) z := by
  have ha : AnalyticAt ℂ (fun w => (A w).det) z := by
    simp only [Matrix.det_fin_two]
    exact ((hA 0 0).mul (hA 1 1)).sub ((hA 0 1).mul (hA 1 0))
  have hb : AnalyticAt ℂ (fun w => (B w).det) z := by
    simp only [Matrix.det_fin_two]
    exact ((hB 0 0).mul (hB 1 1)).sub ((hB 0 1).mul (hB 1 0))
  have hD := spectralMatchingDeterminant_analyticAt R₀ R₁ O₀ O₁ z hR₀ hR₁ hO₀ hO₁
  have hab : AnalyticAt ℂ (fun w => (A w).det*(B w).det) z := ha.mul hb
  have he : (fun w => spectralMatchingDeterminant
      (A w 0 0 • R₀ w+A w 1 0 • R₁ w) (A w 0 1 • R₀ w+A w 1 1 • R₁ w)
      (B w 0 0 • O₀ w+B w 1 0 • O₁ w) (B w 0 1 • O₀ w+B w 1 1 • O₁ w))=
      (fun w => (A w).det*(B w).det)*
        (fun w => spectralMatchingDeterminant (R₀ w) (R₁ w) (O₀ w) (O₁ w)) := by
    funext w
    exact spectralMatchingDeterminant_change _ _ _ _ _ _
  rw [he,analyticOrderAt_mul hab hD,
    hab.analyticOrderAt_eq_zero.mpr (mul_ne_zero hAz hBz),zero_add]

end DefocusingNLS

end OAI
