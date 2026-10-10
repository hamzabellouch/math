import OAI.NumberTheory.CubicMoment.Estimates.CubicBesselSymmetricSlope

namespace OAI

/-! A quantitative Gaussian majorant for the actual negative Whittaker slope. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubic_cosh_exponential_bound {x : ℝ} (hx : 1≤x) (u : ℝ) :
    (x*Real.cosh u-1)*Real.exp (-x*Real.cosh u)*Real.cosh (u/3)≤
      x*Real.exp (-x)*Real.exp (-((x-1)/2-1/18)*u^2) := by
  let y := Real.cosh u
  have hy : 0<y := Real.cosh_pos u
  have he : y≤Real.exp (y-1) := by simpa using Real.add_one_le_exp (y-1)
  have hq := cubic_cosh_quadratic u
  have hc := Real.cosh_le_exp_half_sq (u/3)
  have h0 : 0≤x := by linarith
  calc
    _ ≤ (x*y)*Real.exp (-x*y)*Real.cosh (u/3) := by
      dsimp [y]
      gcongr
      linarith
    _ ≤ (x*Real.exp (y-1))*Real.exp (-x*y)*Real.exp ((u/3)^2/2) := by
      gcongr
    _ = x*Real.exp ((y-1)+(-x*y)+(u/3)^2/2) := by
      rw [mul_assoc,mul_assoc,←Real.exp_add,←Real.exp_add]
      congr 2
      ring
    _ ≤ x*Real.exp (-x+(-((x-1)/2-1/18)*u^2)) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) h0
      have hh := mul_le_mul_of_nonneg_left hq (sub_nonneg.mpr hx)
      dsimp [y]
      nlinarith
    _ = _ := by rw [Real.exp_add,mul_assoc]

lemma cubicWhittakerNegativeSlope_gaussian {v : ℝ} (hv : 0<v)
    (hx : 2≤4*Real.pi*v) :
    -(cubicThetaWhittakerDerivative v).re≤
      (4*Real.pi*v/2)*Real.exp (-4*Real.pi*v)*
        Real.sqrt (Real.pi/((4*Real.pi*v-1)/2-1/18)) := by
  let x := 4*Real.pi*v
  let b := (x-1)/2-1/18
  have hb : 0<b := by dsimp [b,x]; linarith
  have hi := cubicWhittakerNegativeSlope_integral hv
  have hg : Integrable (fun u : ℝ => x*Real.exp (-x)*Real.exp (-b*u^2)) :=
    (integrable_exp_neg_mul_sq hb).const_mul _
  have hm : (∫ u : ℝ,cubicWhittakerNegativeSlope v u)≤
      ∫ u : ℝ,x*Real.exp (-x)*Real.exp (-b*u^2) := by
    apply integral_mono hi.1 hg
    intro u
    simpa only [cubicWhittakerNegativeSlope,x,b,neg_mul] using
      cubic_cosh_exponential_bound (show 1≤x by dsimp [x]; linarith) u
  rw [integral_const_mul,integral_gaussian] at hm
  rw [hi.2]
  have hm' := mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ)≤1/2)
  convert hm' using 1; dsimp [x,b]; simp only [neg_mul]; ring

lemma cubicThetaWhittakerDerivative_gaussian {v : ℝ} (hv : 0<v)
    (hx : 2≤4*Real.pi*v) :
    ‖cubicThetaWhittakerDerivative v‖≤
      (4*Real.pi*v/2)*Real.exp (-4*Real.pi*v)*
        Real.sqrt (Real.pi/((4*Real.pi*v-1)/2-1/18)) := by
  have hn := cubicThetaWhittakerDerivative_re_neg hv (by linarith)
  have he : ‖cubicThetaWhittakerDerivative v‖= -(cubicThetaWhittakerDerivative v).re := by
    change ‖((_:ℝ):ℂ)‖= -(_ : ℝ)
    change _ < 0 at hn
    rw [Complex.norm_real,Real.norm_eq_abs]
    change |(cubicThetaWhittakerDerivative v).re|= -(cubicThetaWhittakerDerivative v).re
    exact abs_of_neg hn
  rw [he]
  exact cubicWhittakerNegativeSlope_gaussian hv hx

end CubicFirstMoment

end

end OAI
