import OAI.Analysis.Mahler.AngularFibers

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter
open scoped Topology ContDiff

/-- The angular function B gives the imaginary part of the rotated complex derivative. -/
theorem rotated_derivative_im {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    r*((deriv MahlerConformal.F (MahlerConformal.polar r θ))*
      Complex.exp ((θ : ℂ)*Complex.I)).im = MahlerConformal.B r θ := by
  have hw : ‖MahlerConformal.polar r θ‖ < 1 := by rwa [MahlerConformal.norm_polar hr.le]
  have hF := (MahlerConformal.hasDerivAt_F_series hw).differentiableAt.hasDerivAt
  have hQ := (hF.comp (θ : ℂ) (MahlerConformal.hasDerivAt_polar_complex r θ)).real_of_complex
  have hq : HasDerivAt (MahlerConformal.Q r)
      ((deriv MahlerConformal.F (MahlerConformal.polar r θ))*
        (Complex.I*MahlerConformal.polar r θ)).re θ := hQ
  have heq := hq.unique (MahlerConformal.hasDerivAt_Q hr hr1 θ)
  have halg : ((deriv MahlerConformal.F (MahlerConformal.polar r θ))*
        (Complex.I*MahlerConformal.polar r θ)).re =
      -r*((deriv MahlerConformal.F (MahlerConformal.polar r θ))*
        Complex.exp ((θ : ℂ)*Complex.I)).im := by
    simp only [MahlerConformal.polar, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [halg] at heq
  linarith

noncomputable def fiberHeight (q r : ℝ) : ℝ :=
  MahlerConformal.S r (fiberAngle q r)

/-- The actual chosen fiber has positive vertical derivative on its open domain. -/
theorem hasDerivAt_fiberHeight {q r : ℝ} (hr : r ∈ fiberDomain q) :
    HasDerivAt (fiberHeight q)
      (r*‖deriv MahlerConformal.F (MahlerConformal.polar r (fiberAngle q r))‖^2 /
        MahlerConformal.B r (fiberAngle q r)) r := by
  have hs := fiberAngle_spec hr
  have hθ := (contDiffAt_fiberAngle hr).differentiableAt (by norm_num) |>.hasDerivAt
  have hw : ‖MahlerConformal.polar r (fiberAngle q r)‖ < 1 := by
    simpa only [MahlerConformal.norm_polar hr.1.le] using hr.2.1
  have hF := (MahlerConformal.hasDerivAt_F_series hw).differentiableAt.hasDerivAt
  have hlevel : ∀ᶠ s in 𝓝 r,
      (MahlerConformal.F (polarCurve (fiberAngle q) s)).re = q := by
    filter_upwards [(fiberDomain_isOpen q).mem_nhds hr] with s hs
    exact (fiberAngle_spec hs).2
  have hB := MahlerConformal.B_pos hr.1 hr.2.1 hs.1.1 hs.1.2
  have hrot := rotated_derivative_im hr.1 hr.2.1 (θ := fiberAngle q r)
  have him : 0 < ((deriv MahlerConformal.F (MahlerConformal.polar r (fiberAngle q r)))*
      Complex.exp ((fiberAngle q r : ℂ)*Complex.I)).im := by nlinarith [hr.1]
  have hv := image_polarCurve_vertical_derivative hF hθ hlevel him
  have hn : Complex.normSq ((deriv MahlerConformal.F (MahlerConformal.polar r (fiberAngle q r)))*
      Complex.exp ((fiberAngle q r : ℂ)*Complex.I)) =
      ‖deriv MahlerConformal.F (MahlerConformal.polar r (fiberAngle q r))‖^2 := by
    rw [Complex.normSq_eq_norm_sq, norm_mul]
    simp [Complex.norm_exp]
  rw [hn] at hv
  have hquot : ‖deriv MahlerConformal.F (MahlerConformal.polar r (fiberAngle q r))‖^2 /
      ((deriv MahlerConformal.F (MahlerConformal.polar r (fiberAngle q r)))*
        Complex.exp ((fiberAngle q r : ℂ)*Complex.I)).im =
      r*‖deriv MahlerConformal.F (MahlerConformal.polar r (fiberAngle q r))‖^2 /
        MahlerConformal.B r (fiberAngle q r) := by
    rw [← hrot]
    field_simp [hr.1.ne']
  rw [hquot] at hv
  exact hv

theorem deriv_fiberHeight_pos {q r : ℝ} (hr : r ∈ fiberDomain q) :
    0 < deriv (fiberHeight q) r := by
  rw [(hasDerivAt_fiberHeight hr).deriv]
  have hs := fiberAngle_spec hr
  have hw : ‖MahlerConformal.polar r (fiberAngle q r)‖ < 1 := by
    simpa only [MahlerConformal.norm_polar hr.1.le] using hr.2.1
  exact div_pos (mul_pos hr.1 (sq_pos_of_pos (norm_pos_iff.mpr (MahlerConformal.deriv_F_ne_zero hw))))
    (MahlerConformal.B_pos hr.1 hr.2.1 hs.1.1 hs.1.2)

theorem contDiffAt_fiberHeight {q r : ℝ} (hr : r ∈ fiberDomain q) :
    ContDiffAt ℝ ∞ (fiberHeight q) r := by
  have hp := contDiffAt_id.prodMk (contDiffAt_fiberAngle hr)
  have hS := contDiffAt_S_uncurry (θ := fiberAngle q r) hr.1 hr.2.1
  have hc := hS.comp r hp
  exact hc

/-- Each constructed upper vertical fiber is traversed strictly upward. -/
theorem strictMonoOn_fiberHeight {q r₀ : ℝ} (hr₀ : 0 ≤ r₀)
    (hq : radialMap r₀ = |q|) : StrictMonoOn (fiberHeight q) (Ioo r₀ 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
  · intro r hr
    exact (hasDerivAt_fiberHeight (mem_fiberDomain_of_basepoint hr₀ hq hr)).continuousAt.continuousWithinAt
  · intro r hr
    rw [interior_Ioo] at hr
    exact deriv_fiberHeight_pos (mem_fiberDomain_of_basepoint hr₀ hq hr)

end SymmetricMahler

end OAI
