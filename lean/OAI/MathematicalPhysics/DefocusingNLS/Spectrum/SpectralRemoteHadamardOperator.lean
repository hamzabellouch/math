import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteBlockOperator
import Mathlib.LinearAlgebra.Matrix.Hadamard

namespace OAI

/-! A fixed linear map lifts entrywise multipliers to Sylvester operators. -/

namespace DefocusingNLS

noncomputable def spectralRemoteHadamardMatrix
    (M : Matrix SpectralRemoteIndex SpectralRemoteIndex ℂ) :
    (Matrix SpectralRemoteIndex SpectralRemoteIndex ℂ) →L[ℂ]
      Matrix SpectralRemoteIndex SpectralRemoteIndex ℂ :=
  LinearMap.toContinuousLinearMap {
    toFun := fun N => M.hadamard N
    map_add' := by intro N P; exact Matrix.hadamard_add M N P
    map_smul' := by intro c N; exact Matrix.hadamard_smul M N c }

noncomputable def spectralRemoteHadamardOperator
    (M : Matrix SpectralRemoteIndex SpectralRemoteIndex ℂ) : SpectralRemoteSuperOperator :=
  spectralRemoteMatrixOperatorL.comp
    (((spectralRemoteHadamardMatrix M).restrictScalars ℝ).comp spectralRemoteOperatorMatrixL)

theorem spectralRemoteHadamardOperator_apply
    (M : Matrix SpectralRemoteIndex SpectralRemoteIndex ℂ) (A : SpectralRemoteOperator) :
    spectralRemoteHadamardOperator M A =
      spectralRemoteMatrixOperator (M.hadamard (spectralRemoteOperatorMatrix A)) := rfl

noncomputable def spectralRemoteHadamardOperatorL :
    (Matrix SpectralRemoteIndex SpectralRemoteIndex ℂ) →L[ℝ] SpectralRemoteSuperOperator :=
  LinearMap.toContinuousLinearMap {
    toFun := spectralRemoteHadamardOperator
    map_add' := by
      intro M N
      apply ContinuousLinearMap.ext
      intro A
      simp only [spectralRemoteHadamardOperator_apply,add_apply,
        Matrix.add_hadamard,spectralRemoteMatrixOperator_add]
    map_smul' := by
      intro c M
      apply ContinuousLinearMap.ext
      intro A
      simp only [spectralRemoteHadamardOperator_apply,smul_apply]
      change spectralRemoteMatrixOperator ((c • M).hadamard (spectralRemoteOperatorMatrix A)) =
        c • spectralRemoteMatrixOperator (M.hadamard (spectralRemoteOperatorMatrix A))
      rw [Matrix.smul_hadamard]
      exact map_smul spectralRemoteMatrixOperatorL c _ }

noncomputable def spectralRemoteGapMatrix (lambda : SpectralRemoteIndex → ℂ) :
    Matrix SpectralRemoteIndex SpectralRemoteIndex ℂ :=
  fun i j => if spectralRemoteBlock i = spectralRemoteBlock j then 0 else -(lambda i-lambda j)⁻¹

theorem spectralRemoteSylvesterOperator_hadamard (r : ℝ) (lambda : SpectralRemoteIndex → ℂ) :
    spectralRemoteSylvesterOperator r lambda =
      spectralRemoteHadamardOperator (((r : ℂ)^2)⁻¹ • spectralRemoteGapMatrix lambda) := by
  apply ContinuousLinearMap.ext
  intro A
  change spectralRemoteMatrixOperator (spectralRemoteOffChange r lambda (spectralRemoteOperatorMatrix A)) = _
  rw [spectralRemoteHadamardOperator_apply]
  congr 1
  ext i j
  by_cases h : spectralRemoteBlock i = spectralRemoteBlock j
  · simp [spectralRemoteOffChange,spectralRemoteGapMatrix,h]
  · simp only [spectralRemoteOffChange,spectralRemoteGapMatrix,h,ite_false,
      Matrix.hadamard_apply,Matrix.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_inv_rev]
    ring

end DefocusingNLS

end OAI
