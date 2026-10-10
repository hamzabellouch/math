import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemotePhysicalFrame
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteBlockOperator
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteRootReduction

namespace OAI

/-! Each incoming coordinate of the reduced block system is a scalar equation. -/

namespace DefocusingNLS

noncomputable def spectralRemoteCoordinate (i : SpectralRemoteIndex) : SpectralRemoteSpace →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj i).comp spectralRemoteBasis.equivFun.toContinuousLinearEquiv.toContinuousLinearMap

theorem spectralRemoteCoordinate_apply (i : SpectralRemoteIndex) (z : SpectralRemoteSpace) :
    spectralRemoteCoordinate i z = spectralRemoteBasis.repr z i := rfl

theorem spectralRemoteMatrixOperator_coordinate (M : Matrix SpectralRemoteIndex SpectralRemoteIndex ℂ)
    (z : SpectralRemoteSpace) (i : SpectralRemoteIndex) :
    spectralRemoteCoordinate i (spectralRemoteMatrixOperator M z) =
      ∑ j, M i j*spectralRemoteCoordinate j z := by
  change spectralRemoteBasis.repr (M.toLin spectralRemoteBasis spectralRemoteBasis z) i = _
  rw [Matrix.repr_toLin]
  rfl

theorem spectralRemote_incoming_block (i j : SpectralRemoteIndex) (hi : i.2 = 1) :
    spectralRemoteBlock i = spectralRemoteBlock j ↔ i = j := by
  rcases i with ⟨a,b⟩
  rcases j with ⟨c,d⟩
  dsimp only [Prod.snd] at hi
  subst b
  fin_cases a <;> fin_cases c <;> fin_cases d <;> simp [spectralRemoteBlock]

theorem spectralRemote_incoming_row (A : SpectralRemoteOperator)
    (hA : spectralRemoteBlockOperator A = A) (i : SpectralRemoteIndex) (hi : i.2 = 1)
    (z : SpectralRemoteSpace) :
    spectralRemoteCoordinate i (A z) = spectralRemoteOperatorMatrix A i i*spectralRemoteCoordinate i z := by
  have hm : spectralRemoteBlockPart (spectralRemoteOperatorMatrix A) = spectralRemoteOperatorMatrix A := by
    have hh := congrArg spectralRemoteOperatorMatrix hA
    simpa only [spectralRemoteBlockOperator_apply,spectralRemoteOperatorMatrix_inverse] using hh
  rw [← spectralRemoteMatrixOperator_inverse A,spectralRemoteMatrixOperator_coordinate]
  rw [spectralRemoteOperatorMatrix_inverse]
  apply Finset.sum_eq_single i
  · intro j _ hij
    have hn : spectralRemoteBlock i ≠ spectralRemoteBlock j := by
      intro h
      exact hij ((spectralRemote_incoming_block i j hi).mp h).symm
    have hz := congrFun (congrFun hm i) j
    simp only [spectralRemoteBlockPart,hn,ite_false] at hz
    rw [← hz,zero_mul]
  · simp

theorem spectralRemote_diagonal_coordinate (d : SpectralRemoteIndex → ℂ)
    (z : SpectralRemoteSpace) (i : SpectralRemoteIndex) :
    spectralRemoteCoordinate i (spectralRemoteMatrixOperator (Matrix.diagonal d) z) =
      d i*spectralRemoteCoordinate i z := by
  change spectralRemoteBasis.repr
    ((Matrix.diagonal d).toLin spectralRemoteBasis spectralRemoteBasis z) i = _
  rw [Matrix.repr_toLin,Matrix.mulVec_diagonal]
  rfl

theorem spectralRemote_incoming_equation
    (Y : ℝ → SpectralRemoteSpace) (c : Fin 2 → ℝ) (A R : SpectralRemoteOperator)
    (i : SpectralRemoteIndex) (hi : i.2 = 1) (hA : spectralRemoteBlockOperator A = A)
    (t : ℝ) (hY : HasDerivAt Y ((spectralRemoteLeadingOperator c t+A+R) (Y t)) t) :
    HasDerivAt (fun s => spectralRemoteCoordinate i (Y s))
      (((Real.exp t : ℂ)^2*spectralRemoteDiagonalRoot c i+spectralRemoteOperatorMatrix A i i)*
        spectralRemoteCoordinate i (Y t)+spectralRemoteCoordinate i (R (Y t))) t := by
  have hd := (spectralRemoteCoordinate i).restrictScalars ℝ |>.hasFDerivAt.comp_hasDerivAt t hY
  apply hd.congr_deriv
  simp only [ContinuousLinearMap.coe_restrictScalars',add_apply,map_add,
    spectralRemoteLeadingOperator,spectralRemote_diagonal_coordinate,
    spectralRemote_incoming_row A hA i hi,add_mul]

end DefocusingNLS

end OAI
