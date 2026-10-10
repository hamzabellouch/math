import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningFluxLower
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningErrorLimit

namespace OAI

/-! Uniform constants for the outgoing flux estimate when the spectral
imaginary part stays in the prescribed strip. -/

namespace DefocusingNLS

noncomputable def spectralTurningFluxBase : ℝ := (Real.exp (-(8*288 : ℝ)))^2/6
noncomputable def spectralTurningFluxErrorConstant : ℝ :=
  let C : ℝ := (5/2)*Real.exp (8*288)
  6*(C^2)^2*Real.exp (C^2)
noncomputable def spectralTurningFluxRemoteConstant : ℝ :=
  ((5/2 : ℝ)*Real.exp (8*288))^2*264
noncomputable def spectralTurningFluxNormConstant : ℝ := 10*Real.exp (8*288)

theorem spectralTurningFluxBase_pos : 0 < spectralTurningFluxBase := by
  unfold spectralTurningFluxBase
  positivity

theorem spectralTurning_flux_coarse (gamma J E : ℝ)
    (hg : |gamma| ≤ 8) (hJ : 0 ≤ J) (hJ1 : J ≤ 1) :
    let B := |gamma| * 288
    let C := (5/2 : ℝ)*Real.exp B
    let delta := 6*(C^2)^2*Real.exp (C^2*J)*J+C^2*((32*|gamma|+8)/E^2)
    let D := spectralTurningFluxErrorConstant*J+spectralTurningFluxRemoteConstant/E^2
    spectralTurningFluxBase-D*(spectralTurningFluxNormConstant+D) ≤
      (Real.exp (-B))^2/6-delta*(10*Real.exp B+delta) := by
  dsimp only
  let B := |gamma| * 288
  let C := (5/2 : ℝ)*Real.exp B
  let C₀ := (5/2 : ℝ)*Real.exp (8*288)
  let delta := 6*(C^2)^2*Real.exp (C^2*J)*J+C^2*((32*|gamma|+8)/E^2)
  let D := spectralTurningFluxErrorConstant*J+spectralTurningFluxRemoteConstant/E^2
  have hB : B ≤ 8*288 := mul_le_mul_of_nonneg_right hg (by norm_num)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hC₀ : 0 ≤ C₀ := by dsimp only [C₀]; positivity
  have hCC : C ≤ C₀ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hB) (by norm_num)
  have hsq : C^2 ≤ C₀^2 := pow_le_pow_left₀ hC hCC 2
  have he : C^2*J ≤ C₀^2 := by
    calc
      _ ≤ C₀^2*1 := mul_le_mul hsq hJ1 hJ (sq_nonneg C₀)
      _ = _ := mul_one _
  have hd0 : 0 ≤ delta := by dsimp only [delta]; positivity
  have hdD : delta ≤ D := by
    dsimp only [delta,D,spectralTurningFluxErrorConstant,spectralTurningFluxRemoteConstant]
    change 6*(C^2)^2*Real.exp (C^2*J)*J+C^2*((32*|gamma|+8)/E^2) ≤
      6*(C₀^2)^2*Real.exp (C₀^2)*J+(C₀^2*264)/E^2
    apply add_le_add
    · gcongr
    · rw [mul_div_assoc]
      gcongr
      linarith
  have hbase : spectralTurningFluxBase ≤ (Real.exp (-B))^2/6 := by
    unfold spectralTurningFluxBase
    gcongr
  have hnorm : 10*Real.exp B ≤ spectralTurningFluxNormConstant := by
    unfold spectralTurningFluxNormConstant
    gcongr
  have hD0 : 0 ≤ D := hd0.trans hdD
  have hloss : delta*(10*Real.exp B+delta) ≤ D*(spectralTurningFluxNormConstant+D) := by
    gcongr
  exact sub_le_sub hbase hloss

end DefocusingNLS

end OAI
