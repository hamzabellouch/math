import OAI.Analysis.CircleDomains.Topology.RoundCircleParametrization
import OAI.Analysis.CircleDomains.Topology.UnorientedCircleGreen
import OAI.Analysis.CircleDomains.Sobolev.SourceArea

namespace OAI

/-! The existing signed Green input specializes to the positively
parametrized round disk. Its sign is determined by the radial one-form,
whose boundary integral and area integral are computed here. -/
open Set Filter Function MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem radial_form_unitCircleParam (R : ℝ) :
    planarFormIntegral (fun z => -z.im) (fun z => z.re) (unitCircleParam 0 R) =
      2 * Real.pi * R^2 := by
  have hi (t : ℝ) :
      -(unitCircleParam 0 R t).im * (deriv (unitCircleParam 0 R) t).re +
      (unitCircleParam 0 R t).re * (deriv (unitCircleParam 0 R) t).im = 2*Real.pi*R^2 := by
    rw [(unitCircleParam_hasDerivAt R t).deriv]
    simp only [unitCircleParam, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat,
      mul_zero, mul_one, sub_zero, add_zero,
      zero_add, circleMap_zero_re, circleMap_zero_im]
    calc
      _ = 2*Real.pi*R^2 * (Real.cos (2*Real.pi*t)^2 + Real.sin (2*Real.pi*t)^2) := by ring
      _ = _ := by rw [Real.cos_sq_add_sin_sq]; ring
  simp only [planarFormIntegral, hi, intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul]

 theorem round_disk_green (hgreen : UnorientedFiniteCircleGreenFormula)
    (R : ℝ) (hR : 0 < R) (O : Set ℂ) (hO : IsOpen O) (hRO : closedBall (0 : ℂ) R ⊆ O)
    (P Q : ℂ → ℝ) (hP : ContDiffOn ℝ (⊤ : ℕ∞) P O)
    (hQ : ContDiffOn ℝ (⊤ : ℕ∞) Q O) :
    planarFormIntegral P Q (unitCircleParam 0 R) =
      ∫ z in ball (0 : ℂ) R, fderiv ℝ Q z 1 - fderiv ℝ P z Complex.I := by
  obtain ⟨e, _he, hg⟩ := hgreen (roundDiskChart R hR) (unitCircleParam 0 R)
    (unitCircleParam_regular R hR)
  have specialize (O : Set ℂ) (hO : IsOpen O) (hsub : closedBall (0 : ℂ) R ⊆ O)
      (P Q : ℂ → ℝ) (hP : ContDiffOn ℝ (⊤ : ℕ∞) P O)
      (hQ : ContDiffOn ℝ (⊤ : ℕ∞) Q O) :
      e * planarFormIntegral P Q (unitCircleParam 0 R) =
        ∫ z in ball (0 : ℂ) R, fderiv ℝ Q z 1 - fderiv ℝ P z Complex.I := by
    simpa only [roundDiskChart_interior, iUnion_of_empty, sdiff_empty, Finset.univ_eq_empty,
      Finset.sum_empty, sub_zero] using
      hg 0 Fin.elim0 Fin.elim0 (by intro i; exact Fin.elim0 i)
        (by intro i; exact Fin.elim0 i) (by intro i; exact Fin.elim0 i)
        O hO (by simpa only [roundDiskChart_interior, iUnion_of_empty, sdiff_empty,
          closure_ball (0 : ℂ) hR.ne'] using hsub) P Q hP hQ
  have he1 : e = 1 := by
    have hh := specialize univ isOpen_univ (subset_univ _) (fun z => -z.im) (fun z => z.re)
      Complex.imCLM.contDiff.neg.contDiffOn Complex.reCLM.contDiff.contDiffOn
    have hd (z : ℂ) : fderiv ℝ (fun w : ℂ => w.re) z 1 -
        fderiv ℝ (fun w : ℂ => -w.im) z Complex.I = 2 := by
      rw [fderiv_fun_neg]
      change fderiv ℝ Complex.reCLM z 1 - -(fderiv ℝ Complex.imCLM z Complex.I) = 2
      rw [Complex.reCLM.fderiv, Complex.imCLM.fderiv]
      norm_num
    simp_rw [hd] at hh
    rw [radial_form_unitCircleParam, integral_const] at hh
    simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul,
      real_volume_ball 0 hR.le] at hh
    have hpos : 0 < 2*Real.pi*R^2 := by positivity
    nlinarith
  simpa only [he1, one_mul] using specialize O hO hRO P Q hP hQ

end CircleDomainRigidity

end

end OAI
