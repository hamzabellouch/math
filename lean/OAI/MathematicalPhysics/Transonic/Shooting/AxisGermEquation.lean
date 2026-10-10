import OAI.MathematicalPhysics.Transonic.Shooting.AxisFamilyGerm
import OAI.MathematicalPhysics.Transonic.Shooting.AxisBarriersCore

namespace OAI

section
noncomputable section

namespace SepticProfile.AxisFamily
open Set Metric SourceFamily
open scoped ContDiff

def UniformGerm.realFunction (G : UniformGerm) (a : Parameter) (x : ℝ) : ℝ := (G.G a (x:ℂ)).re

def UniformGerm.velocity (G : UniformGerm) (a : Parameter) (z : ℝ) : ℝ := z*G.realFunction a (z^2)

lemma UniformGerm.real_analytic (G : UniformGerm) (a : Parameter) {x : ℝ}
    (hx : |x|<G.radius) : AnalyticAt ℝ (G.realFunction a) x := by
  apply (G.analytic a (x:ℂ) _).re_ofReal
  simpa only [mem_ball_zero_iff,Complex.norm_real,Real.norm_eq_abs] using hx

lemma UniformGerm.real_derivative (G : UniformGerm) (a : Parameter) {x : ℝ}
    (hx : |x|<G.radius) : deriv (G.realFunction a) x=(deriv (G.G a) (x:ℂ)).re := by
  apply ((G.analytic a (x:ℂ) _).differentiableAt.hasDerivAt.real_of_complex).deriv
  simpa only [mem_ball_zero_iff,Complex.norm_real,Real.norm_eq_abs] using hx

lemma UniformGerm.velocity_analytic (G : UniformGerm) (a : Parameter) {z : ℝ}
    (hz : z^2<G.radius) : AnalyticAt ℝ (G.velocity a) z := by
  apply analyticAt_id.mul
  apply (G.real_analytic a (x:=z^2) (by simpa only [abs_of_nonneg (sq_nonneg z)] using hz)).comp (f := fun x : ℝ => x^2)
  exact analyticAt_id.pow 2

lemma UniformGerm.velocity_derivative (G : UniformGerm) (a : Parameter) {z : ℝ}
    (hz : z^2<G.radius) : HasDerivAt (G.velocity a)
      (G.realFunction a (z^2)+2*z^2*deriv (G.realFunction a) (z^2)) z := by
  have hd := (G.real_analytic a (x:=z^2) (by simpa only [abs_of_nonneg (sq_nonneg z)] using hz)).differentiableAt.hasDerivAt
  convert (hasDerivAt_id z).mul (hd.comp (h := fun x : ℝ => x^2) z ((hasDerivAt_id z).pow 2)) using 1 <;>
    first | rfl | (simp only [id_eq,Function.comp_def];ring)

lemma UniformGerm.velocity_equation (G : UniformGerm) (a : Parameter) {z : ℝ}
    (hz : z^2<G.radius) :
    AxisBarriers.D (sig a) z (G.velocity a z)*deriv (G.velocity a) z=
      AxisBarriers.N (kap a) z (G.velocity a z) := by
  have hx : |z^2|<G.radius := by simpa only [abs_of_nonneg (sq_nonneg z)] using hz
  have he := G.equation a ((z^2:ℝ):ℂ) (by
    simpa only [mem_ball_zero_iff,Complex.norm_real,Real.norm_eq_abs] using hx)
  have huv : G.G a ((z^2:ℝ):ℂ)=(G.realFunction a (z^2):ℂ) := by
    apply Complex.ext
    · rfl
    · exact G.real a (z^2)
  have he' := congrArg Complex.re he
  rw [huv] at he'
  unfold NormalizedAxis.A at he'
  simp only [← Complex.ofReal_one,← Complex.ofReal_add,← Complex.ofReal_mul,
    ← Complex.ofReal_sub,← Complex.ofReal_pow,← Complex.ofReal_ofNat] at he'
  simp only [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,mul_zero,sub_zero,Complex.div_re,Complex.normSq_ofReal] at he'
  rw [← G.real_derivative a hx] at he'
  rw [(G.velocity_derivative a hz).deriv]
  unfold AxisBarriers.D AxisBarriers.N UniformGerm.velocity
  linear_combination z*he'

end SepticProfile.AxisFamily

end
end

end OAI
