import OAI.Analysis.Laughlin.Fock.MatrixQuadratic
import OAI.Analysis.Laughlin.FourBody.EndExpansion
import OAI.Analysis.Laughlin.FourBody.WedgeCompression

namespace OAI

namespace Laughlin.Fock
open scoped Matrix BigOperators ComplexOrder
open Matrix Spin

noncomputable def physicalFourOccupationColumns (Q D : ℕ) :
    Matrix (FourOccupation Q D) (Fin ((D+1)/2)) ℂ :=
  fun A i => physicalWedgeColumns Q D A.val i

theorem physicalFourOccupationColumns_positive (Q D : ℕ) (hQ : D+1 ≤ Q)
    (hD₁ : 1 ≤ D) (hD₂ : D ≤ 23) :
    (physicalFourOccupationColumns Q D * physicalLimitMiddle D *
      (physicalFourOccupationColumns Q D)ᴴ).PosSemidef := by
  have h := (source_physical_wedge_compression Q D hQ hD₁ hD₂).submatrix
    (fun A : FourOccupation Q D => A.val)
  convert h using 1
  ext A B
  simp [physicalFourOccupationColumns,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.submatrix_apply]

theorem limitFourCopyEnd_matrix_expansion (Q D : ℕ) (i : Fin ((D+1)/2)) (x : Space Q) :
    limitFourCopyEnd Q (Certificate.copyLabel i) D x =
      ∑ A : FourOccupation Q D, star (physicalFourOccupationColumns Q D A i) • fourOccupationEnd Q D A x := by
  have hi : Certificate.copyLabel i ≤ D := by unfold Certificate.copyLabel; have := i.isLt; omega
  have hoi : Odd (Certificate.copyLabel i) := ⟨i.val,by unfold Certificate.copyLabel; omega⟩
  rw [limitFourCopyEnd_expansion Q _ D hi hoi]
  simp only [physicalFourOccupationColumns,physicalWedgeColumns,
    limitFourColumn_occupation_coefficient Q _ D hi hoi,Complex.star_def,Complex.conj_ofReal]

theorem source_fourBody_limitpositive (Q D : ℕ) (hQ : D+1 ≤ Q)
    (hD₁ : 1 ≤ D) (hD₂ : D ≤ 23) (x : Space Q) :
    0 ≤ (∑ i : Fin ((D+1)/2), ∑ j : Fin ((D+1)/2), physicalLimitMiddle D i j *
      occupationInner Q (limitFourCopyEnd Q (Certificate.copyLabel i) D x)
        (limitFourCopyEnd Q (Certificate.copyLabel j) D x)).re := by
  simp_rw [limitFourCopyEnd_matrix_expansion]
  rw [occupation_matrix_quadratic_factor]
  exact occupation_matrix_quadratic_positive Q _
    (physicalFourOccupationColumns_positive Q D hQ hD₁ hD₂) _

end Laughlin.Fock

end OAI
