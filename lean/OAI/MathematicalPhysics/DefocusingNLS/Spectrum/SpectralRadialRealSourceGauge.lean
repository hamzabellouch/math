import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialSourceGauge
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCircularSourceGauge

namespace OAI

/-! Generalized eigenmodes in real gauge coordinates have the same source coordinates. -/

namespace DefocusingNLS

theorem spectralRadialRealSourceGauge (a b : ℝ) (m : ℕ) (η lam : ℂ)
    (Q f g F G : ℝ → ℂ) (hQ : ContDiff ℝ 2 Q)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (he : IsHarmonicRadialSourcePair a b m Q η lam
      (fun r => Q r*(f r+Complex.I*g r)) (fun r => star (Q r)*(f r-Complex.I*g r))
      (fun r => Q r*(F r+Complex.I*G r)) (fun r => star (Q r)*(F r-Complex.I*G r)))
    (r : ℝ) (hr : 0 < r) (hQn : Q r ≠ 0)
    (hstat : Complex.I*(deriv (deriv Q) r+11/(r : ℂ)*deriv Q r)-
      (r : ℂ)/2*deriv Q r+(-(a : ℂ)+Complex.I*(b : ℂ))*Q r-
      Complex.I*((‖Q r‖^(2*m) : ℝ) : ℂ)*Q r=0) :
    (lam*f r+F r=-(deriv (deriv g) r+
      (11/(r : ℂ)+deriv Q r/Q r+star (deriv Q r)/star (Q r))*deriv g r-
      η/(r : ℂ)^2*g r)-
      ((r : ℂ)/2-Complex.I*(deriv Q r/Q r-star (deriv Q r)/star (Q r)))*deriv f r) ∧
    (lam*g r+G r=deriv (deriv f) r+
      (11/(r : ℂ)+deriv Q r/Q r+star (deriv Q r)/star (Q r))*deriv f r-
      η/(r : ℂ)^2*f r-
      ((r : ℂ)/2-Complex.I*(deriv Q r/Q r-star (deriv Q r)/star (Q r)))*deriv g r-
      2*(m : ℂ)*((‖Q r‖^(2*m) : ℝ) : ℂ)*f r) := by
  let U := fun t => f t+Complex.I*g t
  let V := fun t => f t-Complex.I*g t
  have hU : ContDiff ℝ 2 U := hf.add (contDiff_const.mul hg)
  have hV : ContDiff ℝ 2 V := hf.sub (contDiff_const.mul hg)
  have hdu : deriv U=fun t => deriv f t+Complex.I*deriv g t := by
    funext t
    exact ((hf.differentiable (by norm_num) t).hasDerivAt.add
      ((hg.differentiable (by norm_num) t).hasDerivAt.const_mul Complex.I)).deriv
  have hdv : deriv V=fun t => deriv f t-Complex.I*deriv g t := by
    funext t
    exact ((hf.differentiable (by norm_num) t).hasDerivAt.sub
      ((hg.differentiable (by norm_num) t).hasDerivAt.const_mul Complex.I)).deriv
  have hf2 := (hf.deriv' (n := 1)).differentiable (by norm_num)
  have hg2 := (hg.deriv' (n := 1)).differentiable (by norm_num)
  have hddu : deriv (deriv U) r=deriv (deriv f) r+Complex.I*deriv (deriv g) r := by
    rw [hdu]
    exact ((hf2 r).hasDerivAt.add ((hg2 r).hasDerivAt.const_mul Complex.I)).deriv
  have hddv : deriv (deriv V) r=deriv (deriv f) r-Complex.I*deriv (deriv g) r := by
    rw [hdv]
    exact ((hf2 r).hasDerivAt.sub ((hg2 r).hasDerivAt.const_mul Complex.I)).deriv
  obtain ⟨hp,hm⟩ := spectralRadialSourceGauge a b m η lam Q U V
    (fun r => F r+Complex.I*G r) (fun r => F r-Complex.I*G r) hQ hU hV he r hr hQn hstat
  apply spectralCircularSourceGaugeSplit (r : ℂ) η lam (m : ℂ)
    ((‖Q r‖^(2*m) : ℝ) : ℂ) (deriv Q r/Q r) (star (deriv Q r)/star (Q r))
    (f r) (deriv f r) (deriv (deriv f) r) (g r) (deriv g r) (deriv (deriv g) r) (F r) (G r)
  · rw [hddu,hdu] at hp
    dsimp only [U,V] at hp
    convert hp using 1
    ring
  · rw [hddv,hdv] at hm
    dsimp only [U,V] at hm
    convert hm using 1
    ring

end DefocusingNLS

end OAI
