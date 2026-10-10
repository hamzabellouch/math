import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteEnergy
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteInitialEquation

namespace OAI

/-! The actual remote leading root matrix is skew in all four coordinates. -/

namespace DefocusingNLS

noncomputable def spectralRemoteLeadingFrequency (c : Fin 2 → ℝ) (t : ℝ)
    (i : SpectralRemoteIndex) : ℝ :=
  (Real.exp t)^2*(if i.1 = 0 then 1 else -1)*
    (-1/4+(if i.2 = 0 then 1 else -1)*Real.sqrt (1/16-c i.1))

theorem spectralRemoteLeadingOperator_skew (c : Fin 2 → ℝ) (t : ℝ) (z : SpectralRemoteSpace) :
    spectralRemoteLeadingOperator c t z = spectralRemoteSkew (spectralRemoteLeadingFrequency c t) z := by
  rw [spectralRemoteLeadingOperator_eq,spectralRemote_diagonal_operator]
  simp only [smul_apply,ContinuousLinearMap.coe_prodMap']
  dsimp only [Prod.map,spectralRemoteSkew,spectralRemoteLeadingFrequency,spectralRemoteDiagonalRoot,
    homogeneousSpectralLocalizationRemoteRoot]
  apply Prod.ext <;> apply Prod.ext <;>
    simp only [homogeneousDiagonal_apply,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,Complex.ofReal_mul,Complex.ofReal_add,
      Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_neg,Complex.ofReal_one,
      Complex.ofReal_ofNat] <;> norm_num <;> ring

end DefocusingNLS

end OAI
