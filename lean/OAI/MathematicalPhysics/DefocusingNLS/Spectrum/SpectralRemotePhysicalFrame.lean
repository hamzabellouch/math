import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteInitialFrame
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteMatrixOperator
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteRootBlocks

namespace OAI

/-! The physical four-coordinate eigenvector frame and its exact diagonalization. -/

namespace DefocusingNLS

noncomputable def spectralRemoteInitialFrame (c : Fin 2 → ℝ) : SpectralRemoteOperator :=
  (spectralRemoteInitialFramePart 1 (c 0)).prodMap
    (spectralRemoteInitialFramePart (-1) (c 1))

noncomputable def spectralRemotePhysicalLeading (c : Fin 2 → ℝ) : SpectralRemoteOperator :=
  (spectralRemoteLeadingPart 1 (c 0)).prodMap
    (spectralRemoteLeadingPart (-1) (c 1))

theorem spectralRemoteBasis_repr (z : SpectralRemoteSpace) (i : SpectralRemoteIndex) :
    spectralRemoteBasis.repr z i =
      if i.1 = 0 then (if i.2 = 0 then z.1.1 else z.1.2)
      else (if i.2 = 0 then z.2.1 else z.2.2) := by
  rcases i with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [spectralRemoteBasis,spectralRemoteIndexEquiv,
      Module.Basis.coe_finTwoProd_repr]

theorem spectralRemote_diagonal_operator (d : SpectralRemoteIndex → ℂ) :
    spectralRemoteMatrixOperator (Matrix.diagonal d) =
      (homogeneousDiagonal (d (0,0)) (d (0,1))).prodMap
        (homogeneousDiagonal (d (1,0)) (d (1,1))) := by
  apply ContinuousLinearMap.ext
  intro z
  apply spectralRemoteBasis.repr.injective
  ext i
  change spectralRemoteBasis.repr
    ((Matrix.diagonal d).toLin spectralRemoteBasis spectralRemoteBasis z) i = _
  rw [Matrix.repr_toLin,Matrix.mulVec_diagonal]
  rcases i with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [spectralRemoteBasis_repr,homogeneousDiagonal_apply]

theorem spectralRemoteInitialFrame_diagonalizes (c : Fin 2 → ℝ)
    (hc : ∀ i, c i ≤ 1/16) :
    spectralRemotePhysicalLeading c*spectralRemoteInitialFrame c =
      spectralRemoteInitialFrame c*
        spectralRemoteMatrixOperator (Matrix.diagonal (spectralRemoteDiagonalRoot c)) := by
  rw [spectralRemote_diagonal_operator]
  have hp := spectralRemoteInitialFramePart_diagonalizes 1 (c 0) (by norm_num) (hc 0)
  have hm := spectralRemoteInitialFramePart_diagonalizes (-1) (c 1) (by norm_num) (hc 1)
  apply ContinuousLinearMap.ext
  intro z
  change ((spectralRemoteLeadingPart 1 (c 0)*spectralRemoteInitialFramePart 1 (c 0)) z.1,
      (spectralRemoteLeadingPart (-1) (c 1)*spectralRemoteInitialFramePart (-1) (c 1)) z.2) = _
  rw [hp,hm]
  rfl

noncomputable def spectralRemoteInitialFrameInverse (c : Fin 2 → ℝ) : SpectralRemoteOperator :=
  (spectralValueInverse (1,homogeneousSpectralLocalizationRemoteRoot 1 1 (c 0))
    (1,homogeneousSpectralLocalizationRemoteRoot 1 (-1) (c 0))).prodMap
  (spectralValueInverse (1,homogeneousSpectralLocalizationRemoteRoot (-1) 1 (c 1))
    (1,homogeneousSpectralLocalizationRemoteRoot (-1) (-1) (c 1)))

theorem spectralRemoteInitialFrame_unit (c : Fin 2 → ℝ)
    (hc : ∀ i, |c i| ≤ 1/32) : IsUnit (spectralRemoteInitialFrame c) := by
  have hp := (homogeneousSpectralLocalizationRemoteFrame_bounds 1 (c 0) (by norm_num) (hc 0)).1
  have hm := (homogeneousSpectralLocalizationRemoteFrame_bounds (-1) (c 1) (by norm_num) (hc 1)).1
  apply isUnit_iff_exists.mpr
  refine ⟨spectralRemoteInitialFrameInverse c,?_,?_⟩
  · apply ContinuousLinearMap.ext
    intro z
    exact Prod.ext (spectralTwoColumns_apply_inverse _ _ z.1 hp)
      (spectralTwoColumns_apply_inverse _ _ z.2 hm)
  · apply ContinuousLinearMap.ext
    intro z
    exact Prod.ext (spectralValueInverse_apply_columns _ _ z.1 hp)
      (spectralValueInverse_apply_columns _ _ z.2 hm)

end DefocusingNLS

end OAI
