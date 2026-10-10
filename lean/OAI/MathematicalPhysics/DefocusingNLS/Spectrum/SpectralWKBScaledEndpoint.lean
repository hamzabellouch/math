import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBResidualIntegral
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace OAI

/-! Endpoint algebra for the turning scale, shared by the two outer intervals. -/

namespace DefocusingNLS

theorem spectralWKB_scaled_endpoint (r₀ d M p g : ℝ)
    (hr₀ : 0<r₀) (hd : 0<d) (hM : 0<M) (hp : 0<p) (hg : 0≤g)
    (hscale : g*d^3=1) (hlow : (g/8)*(M*d)≤p^2) :
    5*(8*g)/(24*p^3)+(6/r₀)/(2*p)≤
      5/(3*(Real.sqrt (M/8))^3)+3*d/(r₀*Real.sqrt (M/8)) := by
  let s := Real.sqrt (M/8)
  have hs : 0<s := Real.sqrt_pos.2 (by positivity)
  have hprod : s≤p*d := by
    apply Real.sqrt_le_iff.2
    refine ⟨mul_nonneg hp.le hd.le,?_⟩
    have hl := mul_le_mul_of_nonneg_right hlow (sq_nonneg d)
    have he : (g/8*(M*d))*d^2=M/8 := by
      calc
        _ = M/8*(g*d^3) := by ring
        _ = M/8 := by rw [hscale,mul_one]
    rw [he] at hl
    simpa only [mul_pow] using hl
  have hcube := pow_le_pow_left₀ hs.le hprod 3
  have hgp : g*s^3≤p^3 := by
    calc
      _ ≤ g*(p*d)^3 := mul_le_mul_of_nonneg_left hcube hg
      _ = p^3*(g*d^3) := by ring
      _ = p^3 := by rw [hscale,mul_one]
  have h1 : g/p^3≤1/s^3 := (div_le_div_iff₀ (pow_pos hp 3) (pow_pos hs 3)).mpr (by simpa using hgp)
  have h2 : 1/p≤d/s := (div_le_div_iff₀ hp hs).mpr (by simpa only [one_mul,mul_comm d p] using hprod)
  calc
    _ = (5/3)*(g/p^3)+(3/r₀)*(1/p) := by ring
    _ ≤ (5/3)*(1/s^3)+(3/r₀)*(d/s) := add_le_add
      (mul_le_mul_of_nonneg_left h1 (by norm_num))
      (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ = _ := by dsimp only [s]; ring

end DefocusingNLS

end OAI
