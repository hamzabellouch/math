import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBResidualIntegral

namespace OAI

/-! Radial symbol bounds imply an integrable inverse-cubic residual. -/

namespace DefocusingNLS

theorem spectralWKB_radial_bound (r p g e : ℝ) (hr : 0<r) (hp : 0<p)
    (hg : 0≤g) (hgp : g≤4*p^2/r) (he : |e|≤(3/r)*g) :
    (5/16 : ℝ)*g^2/p^5+|e|/(4*p^3)≤8/(r^2*p) := by
  have hge : |e|≤(3/r)*(4*p^2/r) :=
    he.trans (mul_le_mul_of_nonneg_left hgp (by positivity))
  have hsq := pow_le_pow_left₀ hg hgp 2
  calc
    _ ≤ (5/16 : ℝ)*(4*p^2/r)^2/p^5+((3/r)*(4*p^2/r))/(4*p^3) := by
      exact add_le_add
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num))
          (by positivity))
        (div_le_div_of_nonneg_right hge (by positivity))
    _ = 8/(r^2*p) := by field_simp [hr.ne',hp.ne']; ring

theorem spectralWKB_far_bound (r p g e : ℝ) (hr : 0<r) (hp : 0<p)
    (hpr : r/8≤p) (hg : 0≤g) (hgp : g≤4*p^2/r) (he : |e|≤(3/r)*g) :
    (5/16 : ℝ)*g^2/p^5+|e|/(4*p^3)≤64/r^3 := by
  calc
    _ ≤ 8/(r^2*p) := spectralWKB_radial_bound r p g e hr hp hg hgp he
    _ ≤ 8/(r^2*(r/8)) := by gcongr
    _ = 64/r^3 := by field_simp [hr.ne',hp.ne']; ring

end DefocusingNLS

end OAI
