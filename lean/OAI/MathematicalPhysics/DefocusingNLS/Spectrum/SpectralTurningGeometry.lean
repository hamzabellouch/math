import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSpectralLocalizationGeometry

namespace OAI

/-! Exact identities and a uniform quadratic error for the Liouville frequency
at its unique turning point. These identify the rescaled limiting equation. -/

namespace DefocusingNLS

theorem spectralTurningFrequency_identity (h b eta omega r₀ r : ℝ)
    (hr₀ : r₀≠0) (hr : r≠0)
    (hzero : homogeneousSpectralLocalizationFrequency h b eta omega r₀=0) :
    homogeneousSpectralLocalizationFrequency h b eta omega r=
      (r₀^2/16)*((r/r₀)^2-1)+((eta+99/4)/r₀^2)*(1-(r₀/r)^2) := by
  have hz : b-h*omega=(eta+99/4)/r₀^2-r₀^2/16 := by
    dsimp only [homogeneousSpectralLocalizationFrequency] at hzero
    linarith
  dsimp only [homogeneousSpectralLocalizationFrequency]
  calc
    _ = r^2/16+(b-h*omega)-(eta+99/4)/r^2 := by ring
    _ = _ := by rw [hz]; field_simp; ring

theorem spectralTurningFrequency_remainder (h b eta omega r₀ delta : ℝ)
    (hr₀ : r₀≠0) (hr : r₀+delta≠0)
    (hzero : homogeneousSpectralLocalizationFrequency h b eta omega r₀=0) :
    homogeneousSpectralLocalizationFrequency h b eta omega (r₀+delta)-
      (r₀/8+2*(eta+99/4)/r₀^3)*delta=
      delta^2*(1/16-(eta+99/4)*(3*r₀+2*delta)/(r₀^3*(r₀+delta)^2)) := by
  rw [spectralTurningFrequency_identity h b eta omega r₀ (r₀+delta) hr₀ hr hzero]
  field_simp
  ring

theorem spectralTurningFrequency_remainder_bound (h b eta omega r₀ delta : ℝ)
    (hr₀ : 0<r₀) (heta : 0≤eta) (hdelta : |delta|≤r₀/2)
    (hzero : homogeneousSpectralLocalizationFrequency h b eta omega r₀=0) :
    |homogeneousSpectralLocalizationFrequency h b eta omega (r₀+delta)-
      (r₀/8+2*(eta+99/4)/r₀^3)*delta|≤
      delta^2*(1/16+16*(eta+99/4)/r₀^4) := by
  have hd := abs_le.mp hdelta
  have hr : 0<r₀+delta := by linarith
  have hL : 0≤eta+99/4 := by linarith
  have hr2 : 0<r₀^2 := sq_pos_of_pos hr₀
  have hx2 : 0<(r₀+delta)^2 := sq_pos_of_pos hr
  have hden : 0<r₀^3*(r₀+delta)^2 := by positivity
  have hnum : 0≤3*r₀+2*delta := by linarith
  have hsq : r₀^2/4≤(r₀+delta)^2 := by nlinarith
  have hf : (3*r₀+2*delta)/(r₀^3*(r₀+delta)^2)≤16/r₀^4 := by
    apply (div_le_div_iff₀ hden (by positivity : 0<r₀^4)).mpr
    have hh := mul_le_mul_of_nonneg_left hsq (show 0≤16*r₀^3 from by positivity)
    have htop := mul_le_mul_of_nonneg_right (show 3*r₀+2*delta≤4*r₀ from by linarith) (show 0≤r₀^4 from by positivity)
    nlinarith
  rw [spectralTurningFrequency_remainder h b eta omega r₀ delta hr₀.ne' hr.ne' hzero,abs_mul,
    abs_of_nonneg (sq_nonneg delta)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg delta)
  have hn : 0≤(eta+99/4)*(3*r₀+2*delta)/(r₀^3*(r₀+delta)^2) := by positivity
  have hb := mul_le_mul_of_nonneg_left hf hL
  simp only [← mul_div_assoc] at hb
  have ha : |(1/16 : ℝ)-(eta+99/4)*(3*r₀+2*delta)/(r₀^3*(r₀+delta)^2)|≤
      |(1/16 : ℝ)|+|(eta+99/4)*(3*r₀+2*delta)/(r₀^3*(r₀+delta)^2)| := by
    simpa only [Real.norm_eq_abs] using
      norm_sub_le (1/16 : ℝ) ((eta+99/4)*(3*r₀+2*delta)/(r₀^3*(r₀+delta)^2))
  exact ha.trans (by
    rw [abs_of_nonneg (by norm_num : (0 : ℝ)≤1/16),abs_of_nonneg hn]
    simpa only [mul_comm (eta+99/4) 16] using add_le_add (le_refl (1/16 : ℝ)) hb)

end DefocusingNLS

end OAI
