import OAI.NumberTheory.CubicMoment.Estimates.CubicBesselLogSlope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

namespace OAI

/-! An even real integral for the negative Whittaker slope. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubic_cosh_quadratic (u : ℝ) : 1+u^2/2≤Real.cosh u := by
  have h := (Real.hasSum_cosh u).summable.sum_le_tsum (Finset.range 2)
    (fun n _ => by rw [pow_mul]; positivity)
  norm_num [Finset.sum_range_succ] at h
  rwa [←Real.cosh_eq_tsum] at h

lemma cubic_even_exp_integral (f : ℝ → ℝ) (he : ∀ u,f (-u)=f u)
    (hi : Integrable (fun u => f u*Real.exp (-u/3))) :
    Integrable (fun u => f u*Real.cosh (u/3)) ∧
    (∫ u : ℝ,f u*Real.exp (-u/3))=∫ u : ℝ,f u*Real.cosh (u/3) := by
  have hi' : Integrable (fun u => f u*Real.exp (u/3)) := by
    convert hi.comp_neg using 1
    funext u
    simp only [he,neg_neg]
  have hf : (fun u => f u*Real.cosh (u/3))=
      (fun u => (f u*Real.exp (-u/3)+f u*Real.exp (u/3))/2) := by
    funext u
    rw [Real.cosh_eq]
    ring_nf
  refine ⟨hf ▸ (hi.add hi').div_const 2,?_⟩
  have hn : (∫ u : ℝ,f u*Real.exp (u/3))=∫ u : ℝ,f u*Real.exp (-u/3) := by
    convert integral_neg_eq_self (fun u : ℝ => f u*Real.exp (-u/3)) volume using 1
    apply integral_congr_ae
    filter_upwards with u
    simp only [he,neg_neg]
  rw [hf,integral_div,integral_add hi hi',hn]
  ring

def cubicWhittakerNegativeSlope (v u : ℝ) : ℝ :=
  (4*Real.pi*v*Real.cosh u-1)*Real.exp (-4*Real.pi*v*Real.cosh u)*Real.cosh (u/3)

lemma cubicWhittakerNegativeSlope_integral {v : ℝ} (hv : 0<v) :
    Integrable (cubicWhittakerNegativeSlope v) ∧
    -(cubicThetaWhittakerDerivative v).re=
      (1/2:ℝ)*(∫ u : ℝ,cubicWhittakerNegativeSlope v u) := by
  let a := 2*Real.pi*v
  have ha : 0<a := by dsimp [a]; positivity
  let f := fun u : ℝ => (2*a*Real.cosh u-1)*Real.exp (-2*a*Real.cosh u)
  have hi : Integrable (fun u => f u*Real.exp (-u/3)) := by
    convert ((cubicBesselLogDerivative_integrable ha).const_mul (-a)).sub
      (cubicBesselLogWeight_integrable ha) using 1
    funext u
    dsimp [f,cubicBesselLogDerivative,cubicBesselLogWeight]
    ring
  have he := cubic_even_exp_integral f (by intro u; simp [f,Real.cosh_neg]) hi
  have hid : cubicWhittakerNegativeSlope v=(fun u => f u*Real.cosh (u/3)) := by
    funext u
    dsimp [cubicWhittakerNegativeSlope,f,a]
    ring_nf
  refine ⟨hid ▸ he.1,?_⟩
  have hD := cubicBesselKernelDerivative_log ha
  have hK := cubicBesselKernel_log ha
  change -(cubicBesselKernel (a^2)/2+a^2*cubicBesselKernelDerivative (a^2))=_
  rw [hid,←he.2]
  have hf : (fun u => f u*Real.exp (-u/3))=
      (fun u => -a*cubicBesselLogDerivative a u-cubicBesselLogWeight a u) := by
    funext u
    dsimp [f,cubicBesselLogDerivative,cubicBesselLogWeight]
    ring
  rw [hf,integral_sub ((cubicBesselLogDerivative_integrable ha).const_mul (-a))
    (cubicBesselLogWeight_integrable ha),integral_const_mul,←hD,←hK]
  ring

end CubicFirstMoment

end

end OAI
