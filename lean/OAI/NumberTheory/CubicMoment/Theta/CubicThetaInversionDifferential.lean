import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInversionHorizontalDerivative
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaJointDifferential

namespace OAI

/-! Transport actual horizontal derivatives through the inversion law.
This is a chain-rule lemma; all its regularity hypotheses are subsequently
supplied by the convergent theta expansion. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicTheta_inversion_horizontal_deriv {F : ℂ × ℝ → ℂ}
    (hF : ∀ p : ℂ × ℝ,0<p.2 → DifferentiableAt ℝ F p)
    (hI : ∀ p : ℂ × ℝ,0<p.2 → F (cubicThetaInversion 1 p)=F p)
    {v : ℝ} (hv : 0<v) (h : ℂ) :
    deriv (fun t : ℝ => F ((t:ℂ)*h,v)) 0=
      deriv (fun t : ℝ => F ((t:ℂ)*(-star h/(v:ℂ)^2),v⁻¹)) 0 := by
  let w : ℂ := -star h/(v:ℂ)^2
  have hp := cubicThetaInversion_horizontal_hasDerivAt one_ne_zero hv h
  simp only [one_pow,one_mul] at hp
  have hf := (hF (0,v⁻¹) (inv_pos.mpr hv)).hasFDerivAt
  have he : cubicThetaInversion 1 ((0:ℂ)*h,v)=(0,v⁻¹) := by
    simpa using cubicThetaInversion_center 1 hv
  have hc := hf.comp_hasDerivAt_of_eq 0 hp he.symm
  have hg : HasDerivAt (fun t : ℝ => ((t:ℂ)*w,v⁻¹)) (w,0) 0 := by
    convert ((Complex.ofRealCLM.hasDerivAt (x:=(0:ℝ))).mul_const w).prodMk
      (hasDerivAt_const (0:ℝ) (v⁻¹)) using 1 <;> simp
  have hc' := hf.comp_hasDerivAt_of_eq 0 hg (by simp)
  have hfun : (fun t : ℝ => F (cubicThetaInversion 1 ((t:ℂ)*h,v)))=
      fun t : ℝ => F ((t:ℂ)*h,v) := by
    funext t
    exact hI _ hv
  change HasDerivAt (fun t : ℝ => F (cubicThetaInversion 1 ((t:ℂ)*h,v)))
    (fderiv ℝ F (0,v⁻¹) (w,0)) 0 at hc
  rw [hfun] at hc
  exact hc.deriv.trans hc'.deriv.symm

end CubicFirstMoment

end

end OAI
