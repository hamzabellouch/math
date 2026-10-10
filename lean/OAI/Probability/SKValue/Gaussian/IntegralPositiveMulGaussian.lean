import Mathlib
import OAI.Probability.SKValue.Evolution.TerminalError

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory Set Filter Finset
open scoped Topology BigOperators
namespace SKValue
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

lemma integral_positive_mul_gaussian {b : ℝ} (hb : 0<b) :
    (∫ x : ℝ in Ioi 0, x*Real.exp (-b*x^2)) = (2*b)⁻¹ := by
  have A (x : ℝ) : HasDerivAt (fun y : ℝ ↦ -(2*b)⁻¹*Real.exp (-b*y^2))
      (x*Real.exp (-b*x^2)) x := by
    convert! (((hasDerivAt_pow 2 x).const_mul (-b)).exp.const_mul (-(2*b)⁻¹)) using 1
    field_simp
    norm_num
    ring
  have B : Tendsto (fun y : ℝ ↦ -(2*b)⁻¹*Real.exp (-b*y^2)) atTop (𝓝 (0 : ℝ)) := by
    have he : Tendsto (fun y : ℝ ↦ Real.exp (-b*y^2)) atTop (𝓝 (0 : ℝ)) :=
      Real.tendsto_exp_atBot.comp
        ((tendsto_pow_atTop (by norm_num : (2 : ℕ)≠0)).const_mul_atTop_of_neg (neg_lt_zero.mpr hb))
    simpa only [mul_zero] using he.const_mul (-(2*b)⁻¹)
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto' (a := (0 : ℝ)) (fun x _ ↦ A x)
    (integrable_mul_exp_neg_mul_sq hb).integrableOn B
  simpa using hi

lemma integral_abs_centered_gaussian (v : ℝ≥0) :
    (∫ x : ℝ, |x| ∂gaussianReal 0 v) = Real.sqrt (2*(v : ℝ)/Real.pi) := by
  by_cases hv : v=0
  · simp [hv,gaussianReal_zero_var]
  have hvp : (0 : ℝ)<v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  rw [integral_gaussianReal_eq_integral_smul hv]
  have he : (fun x : ℝ ↦ gaussianPDFReal 0 v x • |x|) =
      (fun x : ℝ ↦ (Real.sqrt (2*Real.pi*v))⁻¹*(|x| * Real.exp (-(1/(2*v))*|x|^2))) := by
    funext x
    simp only [gaussianPDFReal, smul_eq_mul, sub_zero, sq_abs]
    have hex : -x^2/(2*(v : ℝ)) = -(1/(2*(v : ℝ)))*x^2 := by ring
    rw [hex]
    ring
  rw [he,integral_const_mul, integral_comp_abs (f := fun x : ℝ ↦ x*Real.exp (-(1/(2*(v : ℝ)))*x^2)),
    integral_positive_mul_gaussian (by positivity : (0 : ℝ)<1/(2*v))]
  have hb : (2*(1/(2*(v : ℝ))))⁻¹=(v : ℝ) := by field_simp
  rw [hb]
  have hn : 0≤(Real.sqrt (2*Real.pi*(v : ℝ)))⁻¹*(2*(v : ℝ)) := by positivity
  have hs : ((Real.sqrt (2*Real.pi*(v : ℝ)))⁻¹*(2*(v : ℝ)))^2 = 2*(v : ℝ)/Real.pi := by
    rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity : 0≤2*Real.pi*(v : ℝ))]
    field_simp
  have hr := Real.sq_sqrt (by positivity : 0≤2*(v : ℝ)/Real.pi)
  nlinarith [Real.sqrt_nonneg (2*(v : ℝ)/Real.pi)]

lemma brownian_increment_abs (W : BrownianSpace) {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) :
    (∫ ω, |W.B 1 ω-W.B t.toNNReal ω| ∂W.μ)=Real.sqrt (2*(1-t)/Real.pi) := by
  have h := (W.brownian.hasLaw_sub 1 t.toNNReal).integral_comp
    (f := fun x : ℝ ↦ |x|) (by fun_prop)
  change (∫ ω, |W.B 1 ω-W.B t.toNNReal ω| ∂W.μ)=_ at h
  have hv := integral_abs_centered_gaussian (nndist ((1 : ℝ≥0) : ℝ) (t.toNNReal : ℝ))
  apply h.trans (hv.trans _)
  congr 2
  simp only [NNReal.coe_one, coe_nndist,Real.dist_eq,Real.coe_toNNReal t ht.1,
    abs_of_nonneg (sub_nonneg.mpr ht.2)]

lemma phi_terminal_uniform (W : BrownianSpace) (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) (x : ℝ) :
    |x|≤phi W γ t x ∧ phi W γ t x≤|x|+Real.sqrt (2*(1-t)/Real.pi)+
      (1/2 : ℝ)*∫ s in t..1, γ.coeff s := by
  exact ⟨phi_lower W γ ht x, by simpa only [brownian_increment_abs W ht, γ.tail_cutoff_eq ht] using phi_upper W γ ht x⟩

end SKValue

end

end OAI
