import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteBlocks
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

/-! The exact matrix realization of the four remote coordinates. -/

namespace DefocusingNLS

noncomputable def spectralRemoteIndexEquiv : (Fin 2 ⊕ Fin 2) ≃ SpectralRemoteIndex where
  toFun := Sum.elim (fun j => (0,j)) (fun j => (1,j))
  invFun := fun j => if j.1 = 0 then Sum.inl j.2 else Sum.inr j.2
  left_inv := by intro j; cases j <;> simp
  right_inv := by intro j; rcases j with ⟨i,j⟩; fin_cases i <;> simp

noncomputable def spectralRemoteBasis : Module.Basis SpectralRemoteIndex ℂ SpectralRemoteSpace :=
  ((Module.Basis.finTwoProd ℂ).prod (Module.Basis.finTwoProd ℂ)).reindex spectralRemoteIndexEquiv

noncomputable def spectralRemoteMatrixEquiv :
    (Matrix SpectralRemoteIndex SpectralRemoteIndex ℂ) ≃ₐ[ℂ] SpectralRemoteOperator :=
  (Matrix.toLinAlgEquiv spectralRemoteBasis).trans
    (Module.End.toContinuousLinearMap (𝕜 := ℂ) SpectralRemoteSpace)

noncomputable def spectralRemoteMatrixOperator
    (M : Matrix SpectralRemoteIndex SpectralRemoteIndex ℂ) : SpectralRemoteOperator :=
  spectralRemoteMatrixEquiv M

theorem spectralRemoteMatrixOperator_add (M N : Matrix SpectralRemoteIndex SpectralRemoteIndex ℂ) :
    spectralRemoteMatrixOperator (M+N) = spectralRemoteMatrixOperator M+spectralRemoteMatrixOperator N :=
  map_add spectralRemoteMatrixEquiv M N

theorem spectralRemoteMatrixOperator_smul (c : ℂ) (M : Matrix SpectralRemoteIndex SpectralRemoteIndex ℂ) :
    spectralRemoteMatrixOperator (c • M) = c • spectralRemoteMatrixOperator M :=
  map_smul spectralRemoteMatrixEquiv c M

theorem spectralRemoteMatrixOperator_mul (M N : Matrix SpectralRemoteIndex SpectralRemoteIndex ℂ) :
    spectralRemoteMatrixOperator (M*N) = spectralRemoteMatrixOperator M*spectralRemoteMatrixOperator N :=
  map_mul spectralRemoteMatrixEquiv M N

theorem spectralRemoteMatrixOperator_sub (M N : Matrix SpectralRemoteIndex SpectralRemoteIndex ℂ) :
    spectralRemoteMatrixOperator (M-N) = spectralRemoteMatrixOperator M-spectralRemoteMatrixOperator N :=
  map_sub spectralRemoteMatrixEquiv M N

noncomputable def spectralRemoteMatrixOperatorL :
    (Matrix SpectralRemoteIndex SpectralRemoteIndex ℂ) →L[ℝ] SpectralRemoteOperator :=
  (LinearMap.toContinuousLinearMap spectralRemoteMatrixEquiv.toLinearMap).restrictScalars ℝ

noncomputable def spectralRemoteOperatorMatrix (A : SpectralRemoteOperator) :
    Matrix SpectralRemoteIndex SpectralRemoteIndex ℂ := spectralRemoteMatrixEquiv.symm A

theorem spectralRemoteMatrixOperator_inverse (A : SpectralRemoteOperator) :
    spectralRemoteMatrixOperator (spectralRemoteOperatorMatrix A) = A :=
  spectralRemoteMatrixEquiv.apply_symm_apply A

theorem spectralRemoteOperatorMatrix_inverse (M : Matrix SpectralRemoteIndex SpectralRemoteIndex ℂ) :
    spectralRemoteOperatorMatrix (spectralRemoteMatrixOperator M) = M :=
  spectralRemoteMatrixEquiv.symm_apply_apply M

end DefocusingNLS

end OAI
