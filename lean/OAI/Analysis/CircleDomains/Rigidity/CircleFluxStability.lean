import OAI.Analysis.CircleDomains.Topology.RoundCircleParametrization

namespace OAI

/-! A uniform perturbation of the boundary values changes vertical flux
by at most the circle length times that perturbation. -/
open Set Filter Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem unitCircleParam_deriv_norm {R : ℝ} (hR : 0 ≤ R) (t : ℝ) :
    ‖deriv (unitCircleParam 0 R) t‖ = 2*Real.pi*R := by
  rw [(unitCircleParam_hasDerivAt R t).deriv]
  simp only [norm_mul, norm_circleMap_zero, abs_of_nonneg hR, Complex.norm_I,
    mul_one, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  ring

 theorem unitCircleParam_deriv_continuous (R : ℝ) :
    Continuous (deriv (unitCircleParam 0 R)) := by
  have heq : deriv (unitCircleParam 0 R) =
      fun t => circleMap 0 R (2*Real.pi*t) * Complex.I * (2*Real.pi) := by
    funext t
    exact (unitCircleParam_hasDerivAt R t).deriv
  rw [heq]
  exact (((continuous_circleMap 0 R).comp (continuous_const.mul continuous_id)).mul
    continuous_const).mul continuous_const

 theorem vertical_circle_flux_stability {F G : ℂ → ℂ} {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 ≤ ε)
    (hF : Continuous (fun t => F (unitCircleParam 0 R t)))
    (hG : Continuous (fun t => G (unitCircleParam 0 R t)))
    (hbound : ∀ t : ℝ, ‖F (unitCircleParam 0 R t) - G (unitCircleParam 0 R t)‖ ≤ ε) :
    |planarFormIntegral (fun z => -(F z).im) (fun _ => 0) (unitCircleParam 0 R) -
      planarFormIntegral (fun z => -(G z).im) (fun _ => 0) (unitCircleParam 0 R)| ≤
      2*Real.pi*R*ε := by
  have hd := Complex.continuous_re.comp (unitCircleParam_deriv_continuous R)
  have hf : IntervalIntegrable (fun t => -(F (unitCircleParam 0 R t)).im *
      (deriv (unitCircleParam 0 R) t).re) volume 0 1 :=
    ((Complex.continuous_im.comp hF).neg.mul hd).intervalIntegrable 0 1
  have hg : IntervalIntegrable (fun t => -(G (unitCircleParam 0 R t)).im *
      (deriv (unitCircleParam 0 R) t).re) volume 0 1 :=
    ((Complex.continuous_im.comp hG).neg.mul hd).intervalIntegrable 0 1
  simp only [planarFormIntegral, zero_mul, add_zero]
  rw [← intervalIntegral.integral_sub hf hg]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := 2*Real.pi*R*ε) (fun t _ht => show
      ‖-(F (unitCircleParam 0 R t)).im * (deriv (unitCircleParam 0 R) t).re -
        -(G (unitCircleParam 0 R t)).im * (deriv (unitCircleParam 0 R) t).re‖ ≤ _ from by
      have heq : -(F (unitCircleParam 0 R t)).im * (deriv (unitCircleParam 0 R) t).re -
          -(G (unitCircleParam 0 R t)).im * (deriv (unitCircleParam 0 R) t).re =
          -(F (unitCircleParam 0 R t)-G (unitCircleParam 0 R t)).im *
            (deriv (unitCircleParam 0 R) t).re := by
        simp only [Complex.sub_im]
        ring
      rw [heq, norm_mul, norm_neg]
      have h1 := mul_le_mul (Complex.abs_im_le_norm (F (unitCircleParam 0 R t)-G (unitCircleParam 0 R t)))
        (Complex.abs_re_le_norm (deriv (unitCircleParam 0 R) t))
        (abs_nonneg _) (norm_nonneg _)
      have h2 := mul_le_mul (hbound t) (le_of_eq (unitCircleParam_deriv_norm hR t))
        (norm_nonneg _) hε
      exact h1.trans (h2.trans_eq (by ring)))
  simpa only [Real.norm_eq_abs, sub_zero, abs_one, one_mul, mul_one] using hb

end CircleDomainRigidity

end

end OAI
