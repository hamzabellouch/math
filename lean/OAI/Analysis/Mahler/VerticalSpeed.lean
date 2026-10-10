import OAI.Analysis.Mahler.RadialBridge
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate

namespace OAI

namespace SymmetricMahler
open Real Complex Set Filter
open scoped Topology

/-- The Cauchy--Riemann algebra on a real-level curve. -/
theorem vertical_speed_algebra {z : ℂ} {t : ℝ}
    (hreal : (z*(1+Complex.I*(t : ℂ))).re = 0) (him : 0 < z.im) :
    (z*(1+Complex.I*(t : ℂ))).im = Complex.normSq z/z.im := by
  simp only [Complex.mul_re, Complex.add_re, Complex.one_re, Complex.I_re,
    Complex.ofReal_re, Complex.mul_im, Complex.I_im, Complex.ofReal_im,
    Complex.add_im, Complex.one_im] at hreal ⊢
  have hmul := congrArg (fun x : ℝ => z.re*x) hreal
  rw [Complex.normSq_apply]
  field_simp
  nlinarith

theorem vertical_speed_algebra_pos {z : ℂ} {t : ℝ}
    (hreal : (z*(1+Complex.I*(t : ℂ))).re = 0) (him : 0 < z.im) :
    0 < (z*(1+Complex.I*(t : ℂ))).im := by
  rw [vertical_speed_algebra hreal him]
  apply div_pos _ him
  rw [Complex.normSq_apply]
  nlinarith [sq_nonneg z.re, sq_pos_of_pos him]

noncomputable def polarCurve (θ : ℝ → ℝ) (r : ℝ) : ℂ :=
  (r : ℂ)*Complex.exp ((θ r : ℂ)*Complex.I)

/-- The derivative of a polar curve with differentiable angle. -/
theorem hasDerivAt_polarCurve {θ : ℝ → ℝ} {r t : ℝ} (hθ : HasDerivAt θ t r) :
    HasDerivAt (polarCurve θ)
      (Complex.exp ((θ r : ℂ)*Complex.I)*(1+Complex.I*((r*t : ℝ) : ℂ))) r := by
  have hc := (Complex.hasDerivAt_exp ((θ r : ℂ)*Complex.I)).comp r
    (hθ.ofReal_comp.mul_const Complex.I)
  have h := (Complex.ofRealCLM.hasDerivAt (x := r)).mul hc
  have heq : Complex.exp ((θ r : ℂ)*Complex.I)*(1+Complex.I*((r*t : ℝ) : ℂ)) =
      Complex.ofRealCLM 1 * (Complex.exp ∘ fun y => (θ y : ℂ)*Complex.I) r +
      Complex.ofRealCLM r * (Complex.exp ((θ r : ℂ)*Complex.I)*((t : ℂ)*Complex.I)) := by
    dsimp only [Complex.ofRealCLM_apply, Function.comp_def]
    push_cast
    ring
  rw [← heq] at h
  exact h

/-- The image curve's derivative is obtained by the actual complex chain rule. -/
theorem hasDerivAt_image_polarCurve {F : ℂ → ℂ} {θ : ℝ → ℝ} {r t : ℝ} {g : ℂ}
    (hF : HasDerivAt F g (polarCurve θ r)) (hθ : HasDerivAt θ t r) :
    HasDerivAt (fun s => F (polarCurve θ s))
      ((g*Complex.exp ((θ r : ℂ)*Complex.I))*(1+Complex.I*((r*t : ℝ) : ℂ))) r := by
  have h := hF.comp r (hasDerivAt_polarCurve hθ)
  rw [mul_assoc]
  exact h

/-- Constancy of the real part forces the image curve to move upward
under the angular derivative sign condition. -/
theorem image_polarCurve_vertical_derivative {F : ℂ → ℂ} {θ : ℝ → ℝ}
    {r t q : ℝ} {g : ℂ}
    (hF : HasDerivAt F g (polarCurve θ r)) (hθ : HasDerivAt θ t r)
    (hlevel : ∀ᶠ s in 𝓝 r, (F (polarCurve θ s)).re = q)
    (him : 0 < (g*Complex.exp ((θ r : ℂ)*Complex.I)).im) :
    HasDerivAt (fun s => (F (polarCurve θ s)).im)
      (Complex.normSq (g*Complex.exp ((θ r : ℂ)*Complex.I)) /
        (g*Complex.exp ((θ r : ℂ)*Complex.I)).im) r := by
  have h := hasDerivAt_image_polarCurve hF hθ
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt r h
  have hconst : HasDerivAt (fun s => (F (polarCurve θ s)).re) 0 r :=
    (hasDerivAt_const r q).congr_of_eventuallyEq hlevel
  have hzero := hre.unique hconst
  have hreal : ((g*Complex.exp ((θ r : ℂ)*Complex.I))*(1+Complex.I*((r*t : ℝ) : ℂ))).re = 0 := hzero
  have himder := Complex.imCLM.hasFDerivAt.comp_hasDerivAt r h
  simpa only [Complex.imCLM_apply, Function.comp_def, vertical_speed_algebra hreal him] using! himder

end SymmetricMahler

end OAI
