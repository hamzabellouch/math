import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleFrequencyJet

namespace OAI

/-! In the frequency-dominated negative channel the potential stays positive
on the entire exterior interval, with a fixed relative slope bound. -/

namespace DefocusingNLS

theorem spectralNoTurn_frequency_lower (b eta omega C R r : ℝ)
    (hb : 0 ≤ b) (hw : 0 < omega) (hR : 0 < R) (hr : R ≤ r)
    (hL : eta+99/4 ≤ C*omega) (hCR : 2*C ≤ R^2) :
    r^2/16+omega/2 ≤ homogeneousSpectralLocalizationFrequency (-1) b eta omega r := by
  have hrp : 0 < r := hR.trans_le hr
  have hRr : R^2 ≤ r^2 := pow_le_pow_left₀ hR.le hr 2
  have hquot : (eta+99/4)/r^2 ≤ omega/2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hrp)).mpr
    have hh := mul_le_mul_of_nonneg_right (hCR.trans hRr) hw.le
    nlinarith
  dsimp only [homogeneousSpectralLocalizationFrequency]
  linarith

theorem spectralNoTurn_slope_bound (b eta omega C R r : ℝ)
    (hb : 0 ≤ b) (heta : 0 ≤ eta) (hw : 0 < omega) (hC : 0 ≤ C)
    (hR : 0 < R) (hr : R ≤ r) (hL : eta+99/4 ≤ C*omega) (hCR : 2*C ≤ R^2) :
    spectralLiouvilleSlope eta r ≤ (2/R+4*C/R^3)*
      homogeneousSpectralLocalizationFrequency (-1) b eta omega r := by
  let F := homogeneousSpectralLocalizationFrequency (-1) b eta omega r
  have hrp : 0 < r := hR.trans_le hr
  have hFlo : r^2/16+omega/2 ≤ F := spectralNoTurn_frequency_lower b eta omega C R r hb hw hR hr hL hCR
  have hF : 0 < F := lt_of_lt_of_le (by positivity) hFlo
  have hfirst : r/8 ≤ 2/R*F := by
    have hprod := mul_le_mul_of_nonneg_left hr hrp.le
    calc
      r/8 ≤ 2*F/R := (le_div_iff₀ hR).mpr (by nlinarith)
      _ = _ := by ring
  have hsecond : 2*(eta+99/4)/r^3 ≤ 4*C/R^3*F := by
    calc
      _ ≤ 2*(eta+99/4)/R^3 := div_le_div_of_nonneg_left (by positivity)
        (pow_pos hR 3) (pow_le_pow_left₀ hR.le hr 3)
      _ ≤ 4*C*F/R^3 := div_le_div_of_nonneg_right (by nlinarith) (pow_nonneg hR.le 3)
      _ = _ := by ring
  dsimp only [spectralLiouvilleSlope]
  calc
    _ ≤ 2/R*F+4*C/R^3*F := add_le_add hfirst hsecond
    _ = _ := by ring

end DefocusingNLS

end OAI
