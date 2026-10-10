import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteMatchedRobin
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalLiouvillePair

namespace OAI

/-! The natural remote radius satisfies the small normalized coefficient
bounds required for the uniform Robin estimate. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralRemote_natural_radius_bounds (ell : ℕ) (omega E : ℝ)
    (hE : 0 < E) (hscale : E^2 = 256*max ((ell : ℝ)+1) |omega|) :
    |omega| *Real.exp (-2*Real.log (E/2)) ≤ 1/64 ∧
    |(ell : ℝ)*(ell+10)| *Real.exp (-4*Real.log (E/2)) ≤ 1/256 := by
  have hp : 0 < E/2 := by positivity
  have he (n : ℕ) : Real.exp (-(n : ℝ)*Real.log (E/2)) = ((E/2)^n)⁻¹ := by
    rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hp]
  have hmax := le_max_right ((ell : ℝ)+1) |omega|
  have hl := le_max_left ((ell : ℝ)+1) |omega|
  have hel : 0 ≤ (ell : ℝ) := Nat.cast_nonneg _
  have hs : 0 ≤ max ((ell : ℝ)+1) |omega| := le_trans (by positivity) hl
  have heta : (ell : ℝ)*(ell+10) ≤ 4*((ell : ℝ)+1)^2 := by nlinarith [sq_nonneg ((ell : ℝ)-1)]
  have hsq : ((ell : ℝ)+1)^2 ≤ (max ((ell : ℝ)+1) |omega|)^2 := by nlinarith
  have he2 := he 2
  have he4 := he 4
  norm_num only [Nat.cast_ofNat] at he2 he4
  constructor
  · rw [he2]
    change |omega|/(E/2)^2 ≤ 1/64
    apply (div_le_iff₀ (pow_pos hp 2)).mpr
    nlinarith
  · rw [he4, abs_of_nonneg (by positivity : 0 ≤ (ell : ℝ)*(ell+10))]
    change (ell : ℝ)*(ell+10)/(E/2)^4 ≤ 1/256
    apply (div_le_iff₀ (pow_pos hp 4)).mpr
    have hfour : E^4 = 256^2*(max ((ell : ℝ)+1) |omega|)^2 := by
      rw [show E^4 = (E^2)^2 by ring, hscale]
      ring
    nlinarith

end DefocusingNLS

end OAI
