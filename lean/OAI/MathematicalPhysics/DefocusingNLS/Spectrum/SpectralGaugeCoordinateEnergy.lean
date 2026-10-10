import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGaugeRobin

namespace OAI

/-! Exact value energy and two-sided derivative estimates for the actual
physical/gauge coordinate map. -/

namespace DefocusingNLS

noncomputable def spectralCoordinateEnergy (x : ℂ × ℂ) : ℝ := ‖x.1‖^2+‖x.2‖^2

theorem spectralCoordinateEnergy_nonneg (x : ℂ × ℂ) : 0 ≤ spectralCoordinateEnergy x := by
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem spectralGaugeColumns_apply (Q : ℂ) (x : ℂ × ℂ) :
    spectralGaugeColumns Q x = (Q*(x.1+Complex.I*x.2),star Q*(x.1-Complex.I*x.2)) := by
  apply Prod.ext <;> simp [spectralGaugeColumns,spectralTwoColumns] <;> ring

theorem spectralGaugeColumns_energy (Q : ℂ) (x : ℂ × ℂ) :
    spectralCoordinateEnergy (spectralGaugeColumns Q x) = 2*‖Q‖^2*spectralCoordinateEnergy x := by
  rw [spectralGaugeColumns_apply]
  simp only [spectralCoordinateEnergy,norm_mul,norm_star,mul_pow]
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im]
  ring

private theorem norm_add_sq (x y : ℂ) : ‖x+y‖^2 ≤ 2*‖x‖^2+2*‖y‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg (x+y)) (norm_add_le x y) 2
  nlinarith [sq_nonneg (‖x‖-‖y‖)]

theorem spectralCoordinateEnergy_add_le (x y : ℂ × ℂ) :
    spectralCoordinateEnergy (x+y) ≤ 2*spectralCoordinateEnergy x+2*spectralCoordinateEnergy y := by
  have h1 := norm_add_sq x.1 y.1
  have h2 := norm_add_sq x.2 y.2
  dsimp only [spectralCoordinateEnergy,Prod.fst_add,Prod.snd_add]
  linarith

theorem spectralCoordinateEnergy_sub_le (x y : ℂ × ℂ) :
    spectralCoordinateEnergy (x-y) ≤ 2*spectralCoordinateEnergy x+2*spectralCoordinateEnergy y := by
  have h := spectralCoordinateEnergy_add_le x (-y)
  simpa only [sub_eq_add_neg,spectralCoordinateEnergy,Prod.fst_neg,Prod.snd_neg,norm_neg] using h

theorem spectralGaugeColumns_derivative_upper (Q dQ : ℂ) (x dx : ℂ × ℂ) :
    spectralCoordinateEnergy (spectralGaugeColumns Q dx+spectralGaugeColumns dQ x) ≤
      4*‖Q‖^2*spectralCoordinateEnergy dx+4*‖dQ‖^2*spectralCoordinateEnergy x := by
  have h := spectralCoordinateEnergy_add_le (spectralGaugeColumns Q dx) (spectralGaugeColumns dQ x)
  rw [spectralGaugeColumns_energy,spectralGaugeColumns_energy] at h
  nlinarith only [h]

theorem spectralGaugeColumns_derivative_lower (Q dQ : ℂ) (x dx : ℂ × ℂ) :
    ‖Q‖^2*spectralCoordinateEnergy dx ≤
      spectralCoordinateEnergy (spectralGaugeColumns Q dx+spectralGaugeColumns dQ x)+
        2*‖dQ‖^2*spectralCoordinateEnergy x := by
  have h := spectralCoordinateEnergy_sub_le
    (spectralGaugeColumns Q dx+spectralGaugeColumns dQ x) (spectralGaugeColumns dQ x)
  rw [add_sub_cancel_right,spectralGaugeColumns_energy,spectralGaugeColumns_energy] at h
  linarith

end DefocusingNLS

end OAI
