import OAI.Analysis.Laughlin.FourBody.PhysicalCertificate
import OAI.Analysis.Laughlin.FourBody.Symmetry
import OAI.Analysis.Laughlin.Operators.MatrixPhysicalCompression
import OAI.Analysis.Laughlin.Operators.RealComplexMatrixPositive

namespace OAI

namespace Laughlin.Fock
open scoped Matrix BigOperators ComplexOrder
open Matrix Spin

noncomputable def physicalWedgeColumns (Q D : ℕ) :
    Matrix (Finset (Fin (Q+1))) (Fin ((D+1)/2)) ℂ :=
  fun A i => (occupationBasis Q).repr (limitFourColumn Q (Certificate.copyLabel i) D) A

noncomputable def physicalLimitMiddle (D : ℕ) : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℂ :=
  (Certificate.certificateDiagonal D - physicalLimitError D).map Complex.ofReal

theorem physicalWedgeColumns_gram (Q D : ℕ) (hQ : D+1 ≤ Q) :
    (physicalWedgeColumns Q D)ᴴ * physicalWedgeColumns Q D =
      (physicalLimitGram Q D).map Complex.ofReal := by
  rw [physicalLimitGram_eq Q D hQ]
  ext i j
  change occupationInner Q (limitFourColumn Q (Certificate.copyLabel i) D)
    (limitFourColumn Q (Certificate.copyLabel j) D) = _
  exact source_fourBody_physical_scaledGram Q D hQ i j

theorem physicalLimitMiddle_hermitian (D : ℕ) : (physicalLimitMiddle D).IsHermitian := by
  apply real_complex_matrix_hermitian
  apply Matrix.IsHermitian.sub
  · simp [Certificate.certificateDiagonal,Matrix.IsHermitian]
  · rw [physicalLimitError_eq]
    ext i j
    simp only [Matrix.conjTranspose_apply,star_trivial,Certificate.scaledError,
      Certificate.weightSqrtDiagonal,Matrix.diagonal_mul,Matrix.mul_diagonal,
      Matrix.map_apply,Certificate.errorRational,Rat.coe_castHom]
    rw [Certificate.Y_symm D (Certificate.copyLabel j) (Certificate.copyLabel i)]
    ring

theorem source_physical_wedge_compression (Q D : ℕ) (hQ : D+1 ≤ Q)
    (hD₁ : 1 ≤ D) (hD₂ : D ≤ 23) :
    (physicalWedgeColumns Q D * physicalLimitMiddle D * (physicalWedgeColumns Q D)ᴴ).PosSemidef := by
  apply matrix_physical_compression _ _ (physicalLimitMiddle_hermitian D)
  rw [physicalWedgeColumns_gram Q D hQ]
  have h := real_complex_matrix_positive _ (source_physical_four_body_certificates Q D hQ hD₁ hD₂)
  have hm : ∀ A B : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℝ,
      (A*B).map Complex.ofReal = A.map Complex.ofReal * B.map Complex.ofReal := by
    intro A B
    ext i j
    simp [Matrix.mul_apply,Matrix.map_apply,Complex.ofReal_sum]
  simpa only [physicalLimitMiddle,hm] using h

end Laughlin.Fock

end OAI
