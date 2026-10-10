import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralNoTurnGeometry

namespace OAI

/-! Uniform signs and sizes of both frequencies on the fixed Case II shell. -/

namespace DefocusingNLS

theorem spectralCaseII_shell_frequency (b eta omega C R B r : ℝ)
    (hb : 0 ≤ b) (hb1 : b ≤ 1) (heta : 0 ≤ eta) (_hC : 0 ≤ C)
    (hR : 0 < R) (hRr : R ≤ r) (hrB : r ≤ B)
    (hlarge : 2*(B^2/16+1) ≤ omega) (hL : eta+99/4 ≤ C*omega)
    (hCR : 2*C ≤ R^2) :
    homogeneousSpectralLocalizationFrequency 1 b eta omega r ≤ -omega/2 ∧
    omega/2 ≤ homogeneousSpectralLocalizationFrequency (-1) b eta omega r ∧
    |homogeneousSpectralLocalizationFrequency 1 b eta omega r| ≤ (C/R^2+2)*omega ∧
    |homogeneousSpectralLocalizationFrequency (-1) b eta omega r| ≤ (C/R^2+2)*omega := by
  have hr : 0 < r := hR.trans_le hRr
  have hB : 0 < B := hr.trans_le hrB
  have hw : 0 < omega := by nlinarith [sq_nonneg B]
  let A := r^2/16+b
  let D := (eta+99/4)/r^2
  have hA0 : 0 ≤ A := by dsimp only [A]; positivity
  have hA : A ≤ omega/2 := by
    have hs := pow_le_pow_left₀ hr.le hrB 2
    dsimp only [A]
    nlinarith
  have hD0 : 0 ≤ D := by dsimp only [D]; positivity
  have hD : D ≤ C/R^2*omega := by
    calc
      D ≤ (eta+99/4)/R^2 := div_le_div_of_nonneg_left (by positivity)
        (sq_pos_of_pos hR) (pow_le_pow_left₀ hR.le hRr 2)
      _ ≤ (C*omega)/R^2 := div_le_div_of_nonneg_right hL (sq_nonneg R)
      _ = _ := by ring
  have hp : homogeneousSpectralLocalizationFrequency 1 b eta omega r = A-omega-D := by
    dsimp only [homogeneousSpectralLocalizationFrequency,A,D]
    ring
  have hm : homogeneousSpectralLocalizationFrequency (-1) b eta omega r = A+omega-D := by
    dsimp only [homogeneousSpectralLocalizationFrequency,A,D]
    ring
  have hminus := spectralNoTurn_frequency_lower b eta omega C R r hb hw hR hRr hL hCR
  refine ⟨by rw [hp]; linarith,by nlinarith [sq_nonneg r],?_,?_⟩
  · rw [hp]
    exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩
  · rw [hm]
    exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩

end DefocusingNLS

end OAI
