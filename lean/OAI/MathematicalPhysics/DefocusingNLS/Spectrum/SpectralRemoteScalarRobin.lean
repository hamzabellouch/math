import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteRobinBridge

namespace OAI

/-! Conversion of the normalized velocity estimate into the actual Liouville Robin error. -/

namespace DefocusingNLS

theorem spectralRemote_scalar_robin
    (h b eta omega E K M : ℝ) (x w : ℂ) (hh : h^2 = 1)
    (hE : 8 ≤ E) (hb : 0 ≤ b) (hb1 : b ≤ 1) (hK : 0 ≤ K)
    (hc : |h*omega/E^2+eta/E^4| ≤ 1/32) (hx : ‖x‖ ≤ M)
    (hw : ‖w-homogeneousSpectralLocalizationRemoteRoot h 1 (h*omega/E^2+eta/E^4)*x‖ ≤ K/E^2*M) :
    ‖homogeneousSpectralLocalizationFactor h E *
      ((E : ℂ)*w+homogeneousSpectralLocalizationSlope h E*x)-
      (h : ℂ)*Complex.I*(Real.sqrt (homogeneousSpectralLocalizationFrequency h b eta omega E) : ℂ)*
        (homogeneousSpectralLocalizationFactor h E*x)‖ ≤
      ‖homogeneousSpectralLocalizationFactor h E‖*((K+22)/E)*M := by
  have hEp : 0 < E := by linarith
  have hM : 0 ≤ M := (norm_nonneg x).trans hx
  let alpha := homogeneousSpectralLocalizationRemoteRoot h 1 (h*omega/E^2+eta/E^4)
  let phase := (E : ℂ)*alpha+homogeneousSpectralLocalizationSlope h E-
    (h : ℂ)*Complex.I*(Real.sqrt (homogeneousSpectralLocalizationFrequency h b eta omega E) : ℂ)
  have hphase : ‖phase‖ ≤ 22/E := spectralRemote_actual_robin_phase_bound h b eta omega E hh hE hb hb1 hc
  have he : homogeneousSpectralLocalizationFactor h E *
      ((E : ℂ)*w+homogeneousSpectralLocalizationSlope h E*x)-
      (h : ℂ)*Complex.I*(Real.sqrt (homogeneousSpectralLocalizationFrequency h b eta omega E) : ℂ)*
        (homogeneousSpectralLocalizationFactor h E*x) =
      homogeneousSpectralLocalizationFactor h E*((E : ℂ)*(w-alpha*x)+phase*x) := by
    dsimp only [phase]
    ring
  rw [he,norm_mul]
  calc
    _ ≤ ‖homogeneousSpectralLocalizationFactor h E‖*
        (‖(E : ℂ)*(w-alpha*x)‖+‖phase*x‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ = ‖homogeneousSpectralLocalizationFactor h E‖*(E*‖w-alpha*x‖+‖phase‖*‖x‖) := by
      rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hEp]
    _ ≤ ‖homogeneousSpectralLocalizationFactor h E‖*(E*(K/E^2*M)+(22/E)*M) := by
      gcongr
    _ = _ := by
      field_simp [hEp.ne']

end DefocusingNLS

end OAI
