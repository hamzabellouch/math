import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteIncomingRow
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteLeadingSkew

namespace OAI

/-! Coordinate norms and the real-part bound for the scalar incoming equation. -/

namespace DefocusingNLS

theorem spectralRemoteCoordinate_norm_le (i : SpectralRemoteIndex) (z : SpectralRemoteSpace) :
    ‖spectralRemoteCoordinate i z‖ ≤ ‖z‖ := by
  rw [spectralRemoteCoordinate_apply,spectralRemoteBasis_repr]
  split_ifs
  · exact (norm_fst_le z.1).trans (norm_fst_le z)
  · exact (norm_snd_le z.1).trans (norm_fst_le z)
  · exact (norm_fst_le z.2).trans (norm_snd_le z)
  · exact (norm_snd_le z.2).trans (norm_snd_le z)

theorem spectralRemoteBasis_norm (i : SpectralRemoteIndex) : ‖spectralRemoteBasis i‖ = 1 := by
  rcases i with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [spectralRemoteBasis,spectralRemoteIndexEquiv,Module.Basis.prod_apply]

theorem spectralRemoteOperatorMatrix_entry (A : SpectralRemoteOperator)
    (i j : SpectralRemoteIndex) :
    spectralRemoteOperatorMatrix A i j = spectralRemoteCoordinate i (A (spectralRemoteBasis j)) := by
  rw [← spectralRemoteMatrixOperator_inverse A,spectralRemoteMatrixOperator_coordinate]
  simp only [spectralRemoteCoordinate_apply,Module.Basis.repr_self, Finsupp.single_apply]
  simp [spectralRemoteOperatorMatrix_inverse]

theorem spectralRemoteOperatorMatrix_entry_bound (A : SpectralRemoteOperator)
    (i j : SpectralRemoteIndex) : ‖spectralRemoteOperatorMatrix A i j‖ ≤ ‖A‖ := by
  rw [spectralRemoteOperatorMatrix_entry]
  exact (spectralRemoteCoordinate_norm_le i _).trans
    ((A.le_opNorm _).trans_eq (by rw [spectralRemoteBasis_norm,mul_one]))

theorem spectralRemote_incoming_coefficient_re (c : Fin 2 → ℝ) (t : ℝ)
    (A : SpectralRemoteOperator) (i : SpectralRemoteIndex) :
    |(((Real.exp t : ℂ)^2*spectralRemoteDiagonalRoot c i+
      spectralRemoteOperatorMatrix A i i) : ℂ).re| ≤ ‖A‖ := by
  have hzero : (((Real.exp t : ℂ)^2*spectralRemoteDiagonalRoot c i) : ℂ).re = 0 := by
    rw [← Complex.ofReal_pow]
    simp only [spectralRemoteDiagonalRoot,homogeneousSpectralLocalizationRemoteRoot,
      Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,
      Complex.I_im,mul_zero,zero_mul,sub_zero,zero_add]
  rw [Complex.add_re,hzero,zero_add]
  exact (Complex.abs_re_le_norm _).trans (spectralRemoteOperatorMatrix_entry_bound A i i)

end DefocusingNLS

end OAI
