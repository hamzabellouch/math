import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleFrequencyJet

namespace OAI

/-! Derivative bounds near and away from the unique Liouville turning point. -/

namespace DefocusingNLS

theorem spectralLiouvilleSlope_near (eta r₀ r : ℝ) (heta : 0≤eta)
    (hr₀ : 0<r₀) (hr : r₀/2≤r) (hr' : r≤2*r₀) :
    spectralLiouvilleSlope eta r₀/8≤ spectralLiouvilleSlope eta r ∧
      spectralLiouvilleSlope eta r≤8*spectralLiouvilleSlope eta r₀ := by
  have hrp : 0<r := by linarith
  have hL : 0≤2*(eta+99/4) := by positivity
  have hl := pow_le_pow_left₀ (by positivity : 0≤r₀/2) hr 3
  have hu := pow_le_pow_left₀ hrp.le hr' 3
  norm_num only [div_pow, mul_pow] at hl hu
  have h1 := div_le_div_of_nonneg_left hL (by positivity : 0<r₀^3/8) hl
  have h2 := div_le_div_of_nonneg_left hL (by positivity : 0<r^3) hu
  have he1 : 2*(eta+99/4)/(r₀^3/8)=8*(2*(eta+99/4)/r₀^3) := by ring
  have he2 : 2*(eta+99/4)/(8*r₀^3)=(2*(eta+99/4)/r₀^3)/8 := by ring
  rw [he1] at h1
  rw [he2] at h2
  dsimp only [spectralLiouvilleSlope]
  constructor <;> linarith

theorem spectralLiouvilleSecond_relative (eta r : ℝ) (heta : 0≤eta) (hr : 0<r) :
    |spectralLiouvilleSecond eta r|≤(3/r)*spectralLiouvilleSlope eta r := by
  have hterm : 0≤6*(eta+99/4)/r^4 := by positivity
  have hnorm : |(1/8 : ℝ)-6*(eta+99/4)/r^4|≤|1/8|+|6*(eta+99/4)/r^4| := by
    simpa only [Real.norm_eq_abs] using norm_sub_le (1/8 : ℝ) (6*(eta+99/4)/r^4)
  simp only [abs_of_nonneg hterm,abs_of_nonneg (by norm_num : (0 : ℝ)≤1/8)] at hnorm
  have he : (3/r)*spectralLiouvilleSlope eta r=3/8+6*(eta+99/4)/r^4 := by
    dsimp only [spectralLiouvilleSlope]
    field_simp [hr.ne']
    ring
  dsimp only [spectralLiouvilleSecond]
  rw [he]
  linarith

theorem spectralLiouvilleSecond_near (eta r₀ r : ℝ) (heta : 0≤eta)
    (hr₀ : 0<r₀) (hr : r₀/2≤r) :
    |spectralLiouvilleSecond eta r|≤(6/r₀)*spectralLiouvilleSlope eta r := by
  have hrp : 0<r := by linarith
  have hs : 0≤ spectralLiouvilleSlope eta r := by dsimp only [spectralLiouvilleSlope]; positivity
  have hd : 3/r≤6/r₀ := (div_le_div_iff₀ hrp hr₀).mpr (by linarith)
  exact (spectralLiouvilleSecond_relative eta r heta hrp).trans (mul_le_mul_of_nonneg_right hd hs)

end DefocusingNLS

end OAI
