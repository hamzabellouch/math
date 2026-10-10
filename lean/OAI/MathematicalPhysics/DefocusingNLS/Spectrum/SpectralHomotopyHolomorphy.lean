import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCountingBoundary

namespace OAI

/-! # Holomorphy in the actual spectral variable -/

namespace DefocusingNLS

attribute [local irreducible] matchingHomotopyColumn spectralHomotopyDeterminant

theorem analyticAt_spectralQ (ell : ℕ) (h b : ℝ) (z : ℂ) :
    AnalyticAt ℂ (spectralQ ell h b) z := by
  unfold spectralQ
  fun_prop

theorem spectralQ_re (ell : ℕ) (h b : ℝ) (z : ℂ) :
    (spectralQ ell h b z).re = z.re + (ell : ℝ) / 2 := by simp [spectralQ]

theorem analyticAt_spectralHomotopyColumn (ell : ℕ) (h b Z ρ : ℝ) (z : ℂ)
    (hh : h ≠ 0) (hZ : Z ≠ 0) (hz : -(1 / 32 : ℝ) ≤ z.re) :
    AnalyticAt ℂ (fun w => matchingHomotopyColumn (ell + 5) 8
      ((h : ℂ) * Complex.I * Z) ρ (spectralQ ell h b w)) z := by
  have hs : ((h : ℂ) * Complex.I * Z).re = 0 := by simp
  have hsim : ((h : ℂ) * Complex.I * Z).im ≠ 0 := by simpa using mul_ne_zero hh hZ
  have hq : -(1 / 32 : ℝ) ≤ (spectralQ ell h b z).re - (ell : ℝ) / 2 := by
    rw [spectralQ_re]
    linarith
  exact (analyticAt_matchingHomotopyColumn ell 8 ((h : ℂ) * Complex.I * Z)
    (spectralQ ell h b z) ρ (by decide) hq hs hsim).comp (analyticAt_spectralQ ell h b z)

/-- Every member of the tail homotopy is holomorphic on a neighborhood of the
closed counting half-plane. -/
theorem analyticAt_spectralHomotopyDeterminant (ell : ℕ) (b Z ρ : ℝ) (z : ℂ)
    (hZ : Z ≠ 0) (hz : -(1 / 32 : ℝ) ≤ z.re) :
    AnalyticAt ℂ (spectralHomotopyDeterminant ell b Z ρ) z := by
  have hp := analyticAt_spectralHomotopyColumn ell 1 b Z ρ z (by norm_num) hZ hz
  have hm := analyticAt_spectralHomotopyColumn ell (-1) b Z ρ z (by norm_num) hZ hz
  have hp₀ := (analyticAt_pi_iff.mp hp) 0
  have hp₁ := (analyticAt_pi_iff.mp hp) 1
  have hm₀ := (analyticAt_pi_iff.mp hm) 0
  have hm₁ := (analyticAt_pi_iff.mp hm) 1
  have hd := (hp₀.mul hm₁).sub (hp₁.mul hm₀)
  unfold spectralHomotopyDeterminant
  convert! hd using 1
  funext w
  simp only [matchingColumnDeterminant, Pi.mul_apply, Pi.sub_apply,
    Complex.ofReal_one, Complex.ofReal_neg, one_mul, neg_one_mul]

end DefocusingNLS

end OAI
