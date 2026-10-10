import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteMatrixOperator
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteFiniteReduction

namespace OAI

/-! The matrix block projection and Sylvester inverse as operators on the
actual four-dimensional remote state space. -/

namespace DefocusingNLS

noncomputable def spectralRemoteOperatorMatrixL :
    SpectralRemoteOperator →L[ℝ] Matrix SpectralRemoteIndex SpectralRemoteIndex ℂ :=
  (LinearMap.toContinuousLinearMap spectralRemoteMatrixEquiv.symm.toLinearMap).restrictScalars ℝ

noncomputable def spectralRemoteBlockMatrixL :
    (Matrix SpectralRemoteIndex SpectralRemoteIndex ℂ) →L[ℝ]
      Matrix SpectralRemoteIndex SpectralRemoteIndex ℂ :=
  (LinearMap.toContinuousLinearMap ({
      toFun := spectralRemoteBlockPart
      map_add' := by
        intro A B
        ext i j
        by_cases h : spectralRemoteBlock i = spectralRemoteBlock j <;>
          simp [spectralRemoteBlockPart,h]
      map_smul' := by
        intro c A
        ext i j
        by_cases h : spectralRemoteBlock i = spectralRemoteBlock j <;>
          simp [spectralRemoteBlockPart,h] } :
        (Matrix SpectralRemoteIndex SpectralRemoteIndex ℂ) →ₗ[ℂ]
          Matrix SpectralRemoteIndex SpectralRemoteIndex ℂ)).restrictScalars ℝ

noncomputable def spectralRemoteBlockOperator : SpectralRemoteSuperOperator :=
  spectralRemoteMatrixOperatorL.comp (spectralRemoteBlockMatrixL.comp spectralRemoteOperatorMatrixL)

theorem spectralRemoteBlockOperator_apply (A : SpectralRemoteOperator) :
    spectralRemoteBlockOperator A =
      spectralRemoteMatrixOperator (spectralRemoteBlockPart (spectralRemoteOperatorMatrix A)) := rfl

theorem spectralRemoteBlockPart_idempotent (M : Matrix SpectralRemoteIndex SpectralRemoteIndex ℂ) :
    spectralRemoteBlockPart (spectralRemoteBlockPart M) = spectralRemoteBlockPart M := by
  ext i j
  by_cases h : spectralRemoteBlock i = spectralRemoteBlock j <;>
    simp [spectralRemoteBlockPart,h]

theorem spectralRemoteBlockOperator_idempotent (A : SpectralRemoteOperator) :
    spectralRemoteBlockOperator (spectralRemoteBlockOperator A) = spectralRemoteBlockOperator A := by
  simp only [spectralRemoteBlockOperator_apply,spectralRemoteOperatorMatrix_inverse,
    spectralRemoteBlockPart_idempotent]

noncomputable def spectralRemoteSylvesterMatrixL (r : ℝ) (lambda : SpectralRemoteIndex → ℂ) :
    (Matrix SpectralRemoteIndex SpectralRemoteIndex ℂ) →L[ℝ]
      Matrix SpectralRemoteIndex SpectralRemoteIndex ℂ :=
  (LinearMap.toContinuousLinearMap ({
      toFun := spectralRemoteOffChange r lambda
      map_add' := by
        intro A B
        ext i j
        by_cases h : spectralRemoteBlock i = spectralRemoteBlock j <;>
          simp [spectralRemoteOffChange,h,add_div,add_comm]
      map_smul' := by
        intro c A
        ext i j
        by_cases h : spectralRemoteBlock i = spectralRemoteBlock j
        · simp [spectralRemoteOffChange,h]
        · simp only [spectralRemoteOffChange,h,ite_false,Matrix.smul_apply,smul_eq_mul,RingHom.id_apply]
          ring } :
        (Matrix SpectralRemoteIndex SpectralRemoteIndex ℂ) →ₗ[ℂ]
          Matrix SpectralRemoteIndex SpectralRemoteIndex ℂ)).restrictScalars ℝ

noncomputable def spectralRemoteSylvesterOperator (r : ℝ) (lambda : SpectralRemoteIndex → ℂ) :
    SpectralRemoteSuperOperator :=
  spectralRemoteMatrixOperatorL.comp
    ((spectralRemoteSylvesterMatrixL r lambda).comp spectralRemoteOperatorMatrixL)

theorem spectralRemoteSylvesterOperator_commutator (r : ℝ) (hr : r ≠ 0)
    (lambda : SpectralRemoteIndex → ℂ)
    (hgap : ∀ i j, spectralRemoteBlock i ≠ spectralRemoteBlock j → lambda i ≠ lambda j)
    (A : SpectralRemoteOperator) :
    let D := spectralRemoteMatrixOperator (Matrix.diagonal (fun i => (r : ℂ)^2*lambda i))
    D*spectralRemoteSylvesterOperator r lambda A-
      spectralRemoteSylvesterOperator r lambda A*D = spectralRemoteBlockOperator A-A := by
  dsimp only
  change spectralRemoteMatrixOperator (Matrix.diagonal (fun i => (r : ℂ)^2*lambda i))*
      spectralRemoteMatrixOperator (spectralRemoteOffChange r lambda (spectralRemoteOperatorMatrix A))-
    spectralRemoteMatrixOperator (spectralRemoteOffChange r lambda (spectralRemoteOperatorMatrix A))*
      spectralRemoteMatrixOperator (Matrix.diagonal (fun i => (r : ℂ)^2*lambda i)) =
    spectralRemoteMatrixOperator (spectralRemoteBlockPart (spectralRemoteOperatorMatrix A))-A
  rw [← spectralRemoteMatrixOperator_mul,← spectralRemoteMatrixOperator_mul,
    ← spectralRemoteMatrixOperator_sub,spectralRemote_sylvester r hr lambda _ hgap,
    spectralRemoteMatrixOperator_sub,spectralRemoteMatrixOperator_inverse]

end DefocusingNLS

end OAI
