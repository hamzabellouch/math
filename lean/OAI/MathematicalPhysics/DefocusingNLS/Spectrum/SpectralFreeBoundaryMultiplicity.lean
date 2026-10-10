import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreePhysicalBasis

namespace OAI

/-! Passing from the H matching determinant to the physical core boundary
preserves analytic vanishing order. The normalization factor is entire and
nonzero, including at the symmetry roots. -/

open Filter Topology
namespace DefocusingNLS

noncomputable def spectralFreeCoreDeterminant (ell : ℕ) (b r : ℝ) (z : ℂ) : ℂ :=
  matchingColumnDeterminant
    (spectralFreeCoreBoundary ell r (spectralFreePositivePhysical ell b z r))
    (spectralFreeCoreBoundary ell r (spectralFreeNegativePhysical ell b z r))

noncomputable def spectralFreeCoreFactor (ell : ℕ) (b r : ℝ) (z : ℂ) : ℂ :=
  let x := radialFreeSlowArgument (Real.log r)
  let qp := spectralQ ell 1 b z
  let qm := spectralQ ell (-1) b z
  (-2*x*(Complex.exp (((ell : ℂ)-2*qp)*(Real.log r : ℂ))*
    Complex.exp (Complex.log x*qp))*
    (Complex.exp (((ell : ℂ)-2*qm)*(Real.log r : ℂ))*
      Complex.exp (star (Complex.log x)*qm))/(r : ℂ))

private theorem conjugate_core_factor (ell : ℕ) (q : ℂ) (r : ℝ) :
    star (Complex.exp (((ell : ℂ)-2*star q)*(Real.log r : ℂ))*
      (radialFreeSlowArgument (Real.log r))^(star q)) =
    Complex.exp (((ell : ℂ)-2*q)*(Real.log r : ℂ))*
      Complex.exp (star (Complex.log (radialFreeSlowArgument (Real.log r)))*q) := by
  rw [Complex.cpow_def_of_ne_zero (radialFreeSlowArgument_ne_zero _) ]
  simp only [star_mul,Complex.star_def,← Complex.exp_conj,map_mul,map_sub,
    Complex.conj_natCast,Complex.conj_ofNat,Complex.conj_conj,Complex.conj_ofReal]
  ring

theorem spectralFreeCoreDeterminant_factor (ell : ℕ) (b r : ℝ) (z : ℂ)
    (hr : 0<r) (hz : -(1/32 : ℝ)≤z.re) :
    spectralFreeCoreDeterminant ell b r z =
      spectralFreeCoreFactor ell b r z*spectralSlowDeterminant ell b (r^2/4) z := by
  have hq (h : ℝ) : -1<(spectralQ ell h b z).re := by
    rw [spectralQ_re]
    linarith [Nat.cast_nonneg (α := ℝ) ell]
  obtain ⟨_,hp⟩ := spectralFreeAngularPhysical_eq_boundaryColumn ell
    (spectralQ ell 1 b z) (hq 1) r
  obtain ⟨_,hm⟩ := spectralFreeSecondPhysical_eq_boundaryColumn ell
    (spectralQ ell (-1) b z) (hq (-1)) r
  unfold spectralFreeCoreDeterminant
  rw [spectralFreePositivePhysical,spectralFreeNegativePhysical_eq,hp,hm,
    spectralFreeCoreBoundary_determinant,conjugate_core_factor]
  rw [Complex.cpow_def_of_ne_zero (radialFreeSlowArgument_ne_zero _)]
  simp only [spectralFreeCoreFactor,spectralSlowDeterminant,
    radialFreeSlowArgument_log r hr,neg_mul,neg_neg]

theorem spectralFreeCoreFactor_analytic_ne_zero (ell : ℕ) (b r : ℝ) (z : ℂ)
    (hr : 0<r) :
    AnalyticAt ℂ (spectralFreeCoreFactor ell b r) z ∧
      spectralFreeCoreFactor ell b r z≠0 := by
  have hp := analyticAt_spectralQ ell 1 b z
  have hm := analyticAt_spectralQ ell (-1) b z
  dsimp only [spectralFreeCoreFactor]
  constructor
  · exact ((analyticAt_const.mul
      (((analyticAt_const.sub (analyticAt_const.mul hp)).mul analyticAt_const).cexp.mul
        (analyticAt_const.mul hp).cexp)).mul
      (((analyticAt_const.sub (analyticAt_const.mul hm)).mul analyticAt_const).cexp.mul
        (analyticAt_const.mul hm).cexp)).div_const
  · exact div_ne_zero
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
        (radialFreeSlowArgument_ne_zero _))
        (mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)))
        (mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)))
      (Complex.ofReal_ne_zero.mpr hr.ne')

theorem spectralFreeCoreDeterminant_order (ell : ℕ) (b r : ℝ) (z : ℂ)
    (hr : 0<r) (hz : -(1/32 : ℝ)<z.re) :
    analyticOrderAt (spectralFreeCoreDeterminant ell b r) z =
      analyticOrderAt (spectralSlowDeterminant ell b (r^2/4)) z := by
  have he : spectralFreeCoreDeterminant ell b r =ᶠ[𝓝 z]
      spectralFreeCoreFactor ell b r*spectralSlowDeterminant ell b (r^2/4) := by
    have hn := Complex.continuous_re.continuousAt.eventually (eventually_gt_nhds hz)
    filter_upwards [hn] with w hw
    exact spectralFreeCoreDeterminant_factor ell b r w hr hw.le
  obtain ⟨ha,hne⟩ := spectralFreeCoreFactor_analytic_ne_zero ell b r z hr
  have hZ : r^2/4≠0 := div_ne_zero (pow_ne_zero 2 hr.ne') (by norm_num)
  rw [analyticOrderAt_congr he,analyticOrderAt_mul ha
    (analyticAt_spectralSlowDeterminant ell b (r^2/4) z hZ hz.le),
    ha.analyticOrderAt_eq_zero.mpr hne,zero_add]

end DefocusingNLS

end OAI
