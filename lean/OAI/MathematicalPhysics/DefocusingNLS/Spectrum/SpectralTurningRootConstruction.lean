import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningScaleLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningRadius
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleFrequencyJet

namespace OAI

/-! Explicit construction of the unique positive turning radius and its
Airy scale for the actual radial frequency. -/

namespace DefocusingNLS

noncomputable def spectralTurningRoot (h b eta omega : ℝ) : ℝ :=
  Real.sqrt (8*(Real.sqrt ((b-h*omega)^2+(eta+99/4)/4)-(b-h*omega)))

theorem spectralTurningRoot_data (h b eta omega : ℝ) (heta : 0 ≤ eta) :
    0 < spectralTurningRoot h b eta omega ∧
      homogeneousSpectralLocalizationFrequency h b eta omega (spectralTurningRoot h b eta omega) = 0 := by
  let t := b-h*omega
  let L := eta+99/4
  let Z := Real.sqrt (t^2+L/4)
  have hL : 0 < L := by dsimp only [L]; linarith
  have hD : 0 < t^2+L/4 := by positivity
  have hZ : Z^2 = t^2+L/4 := Real.sq_sqrt hD.le
  have habs : |t| < Z := (sq_lt_sq₀ (abs_nonneg t) (Real.sqrt_nonneg _)).mp (by
    rw [sq_abs,hZ]
    linarith)
  have ht : t < Z := (le_abs_self t).trans_lt habs
  have harg : 0 < 8*(Z-t) := by positivity
  have hr : 0 < spectralTurningRoot h b eta omega := Real.sqrt_pos.mpr harg
  have hr2 : (spectralTurningRoot h b eta omega)^2 = 8*(Z-t) := Real.sq_sqrt harg.le
  refine ⟨hr,?_⟩
  let r := spectralTurningRoot h b eta omega
  have hpoly : r^4/16+t*r^2-L = 0 := by
    change (spectralTurningRoot h b eta omega)^4/16+t*(spectralTurningRoot h b eta omega)^2-L = 0
    rw [show (spectralTurningRoot h b eta omega)^4 = ((spectralTurningRoot h b eta omega)^2)^2 by ring,hr2]
    nlinarith
  have hmul : r^2*homogeneousSpectralLocalizationFrequency h b eta omega r = r^4/16+t*r^2-L := by
    dsimp only [homogeneousSpectralLocalizationFrequency,t,L]
    have hr' : r ≠ 0 := hr.ne'
    field_simp [hr']
    ring
  apply (mul_left_cancel₀ (pow_ne_zero 2 hr.ne'))
  rw [hmul,mul_zero,hpoly]

noncomputable def spectralTurningRootScale (eta r : ℝ) : ℝ :=
  (spectralLiouvilleSlope eta r ^ (1/3 : ℝ))⁻¹

theorem spectralTurningRootScale_data (eta r : ℝ) (heta : 0 ≤ eta) (hr : 0 < r) :
    0 < spectralTurningRootScale eta r ∧
      spectralLiouvilleSlope eta r*(spectralTurningRootScale eta r)^3 = 1 := by
  have hs : 0 < spectralLiouvilleSlope eta r := by
    dsimp only [spectralLiouvilleSlope]
    positivity
  refine ⟨inv_pos.mpr (Real.rpow_pos_of_pos hs _),?_⟩
  rw [spectralTurningRootScale,inv_pow,← Real.rpow_mul_natCast hs.le]
  norm_num
  exact mul_inv_cancel₀ hs.ne'

end DefocusingNLS

end OAI
