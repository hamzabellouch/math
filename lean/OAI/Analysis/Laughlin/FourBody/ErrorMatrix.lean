import OAI.Analysis.Laughlin.FourBody.ErrorCertificate
import OAI.Analysis.Laughlin.FourBody.Scaled

namespace OAI

namespace Laughlin.Spin
open scoped Matrix Topology
open Filter

theorem sourceCopyWeight_certificate (D : ℕ) (i : Fin ((D+1)/2)) :
    sourceCopyWeight D (Certificate.copyLabel i) = (Certificate.copyWeight D i : ℝ) := by
  simp [sourceCopyWeight,Certificate.copyWeight]

theorem source_fourBody_error_matrix (D : ℕ) (i j : Fin ((D+1)/2)) :
    limitFourError D (Certificate.copyLabel i) (Certificate.copyLabel j) = Certificate.scaledError D i j := by
  have hi : Certificate.copyLabel i ≤ D := by unfold Certificate.copyLabel; have := i.isLt; omega
  have hj : Certificate.copyLabel j ≤ D := by unfold Certificate.copyLabel; have := j.isLt; omega
  have hoi : Odd (Certificate.copyLabel i) := ⟨i.val,by unfold Certificate.copyLabel; omega⟩
  have hoj : Odd (Certificate.copyLabel j) := ⟨j.val,by unfold Certificate.copyLabel; omega⟩
  rw [source_fourBody_error_certificate_identity D _ _ hi hj hoi hoj,
    sourceCopyWeight_certificate,sourceCopyWeight_certificate,
    Real.sqrt_mul (Certificate.copyWeight_nonneg D i)]
  simp only [Certificate.scaledError,Certificate.weightSqrtDiagonal,Matrix.diagonal_mul,
    Matrix.mul_diagonal,Matrix.map_apply,Certificate.errorRational,Rat.coe_castHom]
  ring

theorem physicalFourError_certificate_tendsto (D : ℕ) (i j : Fin ((D+1)/2)) :
    Tendsto (fun Q => physicalFourError Q D (Certificate.copyLabel i) (Certificate.copyLabel j))
      atTop (𝓝 (Certificate.scaledError D i j)) := by
  rw [← source_fourBody_error_matrix D i j]
  apply physicalFourError_tendsto D
  · unfold Certificate.copyLabel; have := i.isLt; omega
  · unfold Certificate.copyLabel; have := j.isLt; omega

end Laughlin.Spin

end OAI
