import Mathlib
import OAI.Probability.SKValue.Evolution.ColeHopf

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace SKValue

lemma shiftedGaussian_hasLaw {h : ℝ} (hh : 0≤h) (x : ℝ) :
    HasLaw (fun z : ℝ ↦ x+Real.sqrt h*z) (gaussianReal x h.toNNReal) standardGaussian := by
  have hl : HasLaw (fun z : ℝ ↦ z) (gaussianReal 0 1) standardGaussian :=
    ⟨measurable_id.aemeasurable,by simp [standardGaussian]⟩
  have he := gaussianReal_const_add (gaussianReal_const_mul hl (Real.sqrt h)) x
  convert! he using 1; simp only [mul_zero,zero_add,mul_one]
  congr 1
  ext
  simp only [NNReal.coe_mk,Real.sq_sqrt hh,Real.coe_toNNReal _ hh]

lemma heat_eq_gaussian {f : ℝ → ℝ} (hf : Measurable f) {h : ℝ} (hh : 0≤h) (x : ℝ) :
    heat h f x=∫ y,f y ∂gaussianReal x h.toNNReal :=
  (shiftedGaussian_hasLaw hh x).integral_comp hf.aestronglyMeasurable

lemma gaussianPDF_square {a h : ℝ} (ha : 0<a) (hh : 0<h) (x y : ℝ) :
    gaussianPDFReal x h.toNNReal y*gaussianPDFReal 0 a.toNNReal y=
      gaussianPDFReal 0 (a+h).toNNReal x*
        gaussianPDFReal (a/(a+h)*x) (a*h/(a+h)).toNNReal y := by
  have hs : a+h≠0 := (add_pos ha hh).ne'
  have hv : a*h/(a+h)≠0 := ne_of_gt (div_pos (mul_pos ha hh) (add_pos ha hh))
  have hroot : Real.sqrt (2*Real.pi*h)*Real.sqrt (2*Real.pi*a)=
      Real.sqrt (2*Real.pi*(a+h))*Real.sqrt (2*Real.pi*(a*h/(a+h))) := by
    rw [←Real.sqrt_mul (by positivity),←Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  have hexp : -(y-x)^2/(2*h)-y^2/(2*a)=
      -x^2/(2*(a+h))-(y-a/(a+h)*x)^2/(2*(a*h/(a+h))) := by
    field_simp
    ring
  simp only [gaussianPDFReal,Real.coe_toNNReal _ ha.le,Real.coe_toNNReal _ hh.le,
    Real.coe_toNNReal _ (add_pos ha hh).le,Real.coe_toNNReal _ (div_pos (mul_pos ha hh) (add_pos ha hh)).le,sub_zero]
  calc
    _ = (Real.sqrt (2*Real.pi*h)*Real.sqrt (2*Real.pi*a))⁻¹*
        Real.exp (-(y-x)^2/(2*h)-y^2/(2*a)) := by
      simp only [sub_eq_add_neg,neg_div,Real.exp_add,mul_inv_rev]
      ring
    _ = (Real.sqrt (2*Real.pi*(a+h))*Real.sqrt (2*Real.pi*(a*h/(a+h))))⁻¹*
        Real.exp (-x^2/(2*(a+h))-(y-a/(a+h)*x)^2/(2*(a*h/(a+h)))) := by rw [hroot,hexp]
    _ = _ := by simp only [sub_eq_add_neg,neg_div,Real.exp_add,mul_inv_rev]; ring

lemma heat_gaussianFactor {a h : ℝ} (ha : 0<a) (hh : 0≤h)
    {f : ℝ → ℝ} (hf : Measurable f) (x : ℝ) :
    heat h (fun y ↦ gaussianPDFReal 0 a.toNNReal y*f y) x=
      gaussianPDFReal 0 (a+h).toNNReal x*
        heat (a*h/(a+h)) f (a/(a+h)*x) := by
  rcases hh.eq_or_lt with rfl | hh
  · simp [heat,ha.ne']
  have hah : 0<a+h := add_pos ha hh
  have hv : 0<a*h/(a+h) := div_pos (mul_pos ha hh) hah
  rw [heat_eq_gaussian (f := fun y ↦ gaussianPDFReal 0 a.toNNReal y*f y)
    ((measurable_gaussianPDFReal _ _).mul hf) hh.le]
  rw [integral_gaussianReal_eq_integral_smul (ne_of_gt (Real.toNNReal_pos.mpr hh))]
  rw [heat_eq_gaussian hf hv.le,integral_gaussianReal_eq_integral_smul (ne_of_gt (Real.toNNReal_pos.mpr hv))]
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [smul_eq_mul]
  rw [←mul_assoc,gaussianPDF_square ha hh x y,mul_assoc]

end SKValue

end

end OAI
