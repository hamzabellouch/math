import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalCoupling
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPhysicalFactor

namespace OAI

/-! The physical odd-power profile supplies the exact coefficient scaling identity. -/

namespace DefocusingNLS

theorem spectralPhysicalFactor_scale (m : ℕ) (hm : 0 < m) (b r : ℝ) (hr : 0 < r) :
    (Complex.exp ((-1/(m : ℂ)+2*Complex.I*(b : ℂ))*(Real.log r : ℂ))*
      star (Complex.exp ((-1/(m : ℂ)+2*Complex.I*(b : ℂ))*(Real.log r : ℂ))))^m=
      1/(r : ℂ)^2 := by
  let A := Complex.exp ((-1/(m : ℂ)+2*Complex.I*(b : ℂ))*(Real.log r : ℂ))
  change (A*star A)^m=1/(r : ℂ)^2
  rw [Complex.star_def,Complex.mul_conj']
  norm_cast
  rw [← pow_mul]
  change ‖A‖^(2*m)=1/r^2
  rw [radialPhysicalFactor_norm_power m hm b r hr]

theorem spectralPhysicalProfile_hasDerivAt (m : ℕ) (hm : 1 ≤ m) (b : ℝ)
    (lam η : ℂ) (q : ℝ → ℂ) (Y : ℝ → (ℂ × ℂ) × (ℂ × ℂ))
    (r : ℝ) (hr : 0 < r)
    (hY : HasDerivAt Y (circularLeadingField (Real.log r) (Y (Real.log r))+
      circularBoundedField (-1/(m : ℂ)+2*Complex.I*(b : ℂ)-2*lam)
        (-1/(m : ℂ)-2*Complex.I*(b : ℂ)-2*lam) η m (q (Real.log r))
        (Y (Real.log r))) (Real.log r)) :
    let νp := -1/(m : ℂ)+2*Complex.I*(b : ℂ)-2*lam
    let νm := -1/(m : ℂ)-2*Complex.I*(b : ℂ)-2*lam
    HasDerivAt (spectralPhysicalPair νp νm Y)
      (spectralPhysicalCircularField νp νm η m
        (Complex.exp ((-1/(m : ℂ)+2*Complex.I*(b : ℂ))*(Real.log r : ℂ))*q (Real.log r))
        r (spectralPhysicalPair νp νm Y r)) r := by
  have hs : star (-1/(m : ℂ)+2*Complex.I*(b : ℂ))=
      -1/(m : ℂ)-2*Complex.I*(b : ℂ) := by
    simp only [star_add,star_div₀,star_neg,star_one,star_natCast,star_mul,star_ofNat,
      Complex.star_def,Complex.conj_I,Complex.conj_ofReal]
    ring
  simpa only [hs] using spectralPhysicalPair_hasDerivAt
    (-1/(m : ℂ)+2*Complex.I*(b : ℂ)) lam η m hm q Y r hr
    (spectralPhysicalFactor_scale m (by omega) b r hr) (by simpa only [hs] using hY)

end DefocusingNLS

end OAI
