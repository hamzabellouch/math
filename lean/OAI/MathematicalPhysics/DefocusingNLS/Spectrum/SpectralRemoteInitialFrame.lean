import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSpectralLocalizationRemote

namespace OAI

/-! Exact diagonalization of each physical remote leading block. -/

namespace DefocusingNLS

noncomputable def spectralRemoteInitialFramePart (h c : ℝ) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  spectralTwoColumns (1,homogeneousSpectralLocalizationRemoteRoot h 1 c)
    (1,homogeneousSpectralLocalizationRemoteRoot h (-1) c)

noncomputable def spectralRemoteLeadingPart (h c : ℝ) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  spectralTwoColumns (0,(c : ℂ)) (1,-(h : ℂ)*Complex.I/2)

theorem spectralRemoteLeadingPart_apply (h c : ℝ) (z : ℂ × ℂ) :
    spectralRemoteLeadingPart h c z = homogeneousSpectralLocalizationRemoteField h c z := by
  apply Prod.ext
  · simp [spectralRemoteLeadingPart,spectralTwoColumns_apply,homogeneousSpectralLocalizationRemoteField]
  · simp only [spectralRemoteLeadingPart,spectralTwoColumns_apply,homogeneousSpectralLocalizationRemoteField,
      Prod.smul_snd,Prod.snd_add,smul_eq_mul]
    ring

theorem spectralRemoteInitialFramePart_diagonalizes (h c : ℝ) (hh : h^2 = 1) (hc : c ≤ 1/16) :
    spectralRemoteLeadingPart h c*spectralRemoteInitialFramePart h c =
      spectralRemoteInitialFramePart h c*homogeneousDiagonal
        (homogeneousSpectralLocalizationRemoteRoot h 1 c)
        (homogeneousSpectralLocalizationRemoteRoot h (-1) c) := by
  have hp := homogeneousSpectralLocalizationRemoteField_eigenvector h 1 c hh (by norm_num) hc
  have hm := homogeneousSpectralLocalizationRemoteField_eigenvector h (-1) c hh (by norm_num) hc
  rw [← spectralRemoteLeadingPart_apply] at hp hm
  apply ContinuousLinearMap.ext
  intro z
  simp only [mul_apply_eq_comp,spectralRemoteInitialFramePart,spectralTwoColumns_apply,
    map_add,map_smul,hp,hm,homogeneousDiagonal_apply,smul_smul]
  congr 1 <;> rw [mul_comm]

end DefocusingNLS

end OAI
