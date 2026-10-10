import OAI.MathematicalPhysics.DefocusingNLS.Profile.SlowGaugeGrowth

namespace OAI

/-! Cancellation of the two matched jets at the initial contour endpoint. -/

namespace DefocusingNLS

theorem gaugedFlux_product_identity (x G H D A : ℂ) :
    (x*star (G*H)*(G*(D+A*H))).re =
      Complex.normSq G*((x*star H*D).re+(x*A).re*Complex.normSq H) := by
  simp only [Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
    Complex.star_def,Complex.conj_re,Complex.conj_im,Complex.normSq_apply]
  ring

theorem gaugedFlux_at_imaginary_boundary (x G H D : ℂ) (M : ℕ)
    (hx : x.re=0) (hx0 : x ≠ 0) :
    (x*star (G*H)*(G*(D+((M : ℂ)/(2*x)-1/2)*H))).re =
      Complex.normSq G*((x*star H*D).re+(M : ℝ)/2*Complex.normSq H) := by
  rw [gaugedFlux_product_identity]
  have he : x*((M : ℂ)/(2*x)-1/2)=(M : ℂ)/2-x/2 := by
    field_simp [hx0]
  rw [he]
  norm_num [Complex.div_re,hx]

theorem paired_gauged_boundary_flux (Z : ℝ) (M : ℕ) (H D : ℂ) (hZ : 0 < Z) :
    let xp : ℂ := -Complex.I*(Z : ℂ)
    let xm : ℂ := Complex.I*(Z : ℂ)
    let Gp := slowGauge M xp
    let Gm := slowGauge M xm
    (xp*star (Gp*H)*(Gp*(D+((M : ℂ)/(2*xp)-1/2)*H))).re+
      (xm*star (Gm*H)*(Gm*(D+((M : ℂ)/(2*xm)-1/2)*H))).re =
      (M : ℝ)/2*(Complex.normSq (Gp*H)+Complex.normSq (Gm*H)) := by
  intro xp xm Gp Gm
  have hxp : xp.re=0 := by simp [xp]
  have hxm : xm.re=0 := by simp [xm]
  have hz : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  have hxp0 : xp ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hz
  have hxm0 : xm ≠ 0 := mul_ne_zero Complex.I_ne_zero hz
  have hnorm : ‖Gp‖=‖Gm‖ := by
    dsimp only [Gp,Gm]
    rw [slowGauge_norm,slowGauge_norm,hxp,hxm]
    have he : xp = -xm := by dsimp [xp,xm]; ring
    rw [he,norm_neg]
  have hsq : Complex.normSq Gp=Complex.normSq Gm := by
    rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq,hnorm]
  rw [gaugedFlux_at_imaginary_boundary xp Gp H D M hxp hxp0,
    gaugedFlux_at_imaginary_boundary xm Gm H D M hxm hxm0,
    Complex.normSq_mul,Complex.normSq_mul,hsq]
  have hcancel : (xp*star H*D).re+(xm*star H*D).re=0 := by
    rw [← Complex.add_re]
    have he : xp*star H*D+xm*star H*D=0 := by dsimp [xp,xm]; ring
    rw [he,Complex.zero_re]
  linear_combination Complex.normSq Gm*hcancel

end DefocusingNLS

end OAI
