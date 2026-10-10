import Mathlib

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic

theorem hasDerivAt_standardGaussianPDF (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have h := (((hasDerivAt_id x).pow 2).neg.div_const 2).exp.const_mul
    ((Real.sqrt (2*Real.pi))⁻¹)
  convert! h using 1
  · funext y
    simp only [gaussianPDFReal,NNReal.coe_one,sub_zero,mul_one,
      Pi.neg_apply,Pi.pow_apply,id_eq]
  · simp only [Pi.neg_apply,Pi.pow_apply,id_eq]
    simp only [gaussianPDFReal,NNReal.coe_one,sub_zero,mul_one]
    norm_num
    ring

theorem integrable_standardGaussian_iff (f : ℝ → ℝ) :
    Integrable f (gaussianReal 0 1) ↔ Integrable (fun x => f x*gaussianPDFReal 0 1 x) := by
  rw [gaussianReal_of_var_ne_zero _ (by norm_num : (1 : ℝ≥0) ≠ 0)]
  rw [integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
    (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp only [gaussianPDF,ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),smul_eq_mul,mul_comm]

theorem gaussian_integral_mul_eq_integral_deriv (f f' : ℝ → ℝ)
    (hd : ∀ x, HasDerivAt f (f' x) x)
    (hi : Integrable f (gaussianReal 0 1))
    (hi' : Integrable f' (gaussianReal 0 1))
    (hix : Integrable (fun x => x*f x) (gaussianReal 0 1)) :
    (∫ x, x*f x ∂gaussianReal 0 1) = ∫ x, f' x ∂gaussianReal 0 1 := by
  have hi₀ := (integrable_standardGaussian_iff f).mp hi
  have hi₁ := (integrable_standardGaussian_iff f').mp hi'
  have hi₂ := (integrable_standardGaussian_iff (fun x => x*f x)).mp hix
  have hx : Integrable (fun x => f x*(-x*gaussianPDFReal 0 1 x)) := by
    convert hi₂.neg using 1
    funext x
    change _ = -(x*f x*gaussianPDFReal 0 1 x)
    ring
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => hd x) (fun x _ => hasDerivAt_standardGaussianPDF x) hx hi₁ hi₀
  have he : (fun x => f x*(-x*gaussianPDFReal 0 1 x)) =
      (fun x => -(gaussianPDFReal 0 1 x*(x*f x))) := by funext x; ring
  rw [he,integral_neg] at h
  have h' := neg_injective h
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simpa only [smul_eq_mul,mul_comm] using h'

theorem integral_tilted_real_eq_div {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (V g : Ω → ℝ) :
    (∫ x, g x ∂μ.tilted V) =
      (∫ x, g x*Real.exp (V x) ∂μ) / ∫ x, Real.exp (V x) ∂μ := by
  rw [integral_tilted]
  simp only [smul_eq_mul]
  calc
    (∫ x, (Real.exp (V x)/(∫ x, Real.exp (V x) ∂μ))*g x ∂μ) =
        ∫ x, (g x*Real.exp (V x))/(∫ x, Real.exp (V x) ∂μ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = _ := integral_div _ _

theorem gaussian_tilted_stein (V V' g g' : ℝ → ℝ)
    (hV : ∀ x, HasDerivAt V (V' x) x) (hg : ∀ x, HasDerivAt g (g' x) x)
    (hi : Integrable (fun x => g x*Real.exp (V x)) (gaussianReal 0 1))
    (hi' : Integrable (fun x => g' x*Real.exp (V x)) (gaussianReal 0 1))
    (hiV : Integrable (fun x => g x*V' x*Real.exp (V x)) (gaussianReal 0 1))
    (hix : Integrable (fun x => x*(g x*Real.exp (V x))) (gaussianReal 0 1)) :
    (∫ x, x*g x ∂(gaussianReal 0 1).tilted V) =
      (∫ x, g' x ∂(gaussianReal 0 1).tilted V) +
      ∫ x, g x*V' x ∂(gaussianReal 0 1).tilted V := by
  have hd (x : ℝ) : HasDerivAt (fun x => g x*Real.exp (V x))
      (g' x*Real.exp (V x)+g x*V' x*Real.exp (V x)) x := by
    convert! (hg x).mul (hV x).exp using 1
    ring
  have h := gaussian_integral_mul_eq_integral_deriv _ _ hd hi (hi'.add hiV) hix
  simp only [integral_tilted_real_eq_div]
  rw [← add_div]
  congr 1
  rw [← integral_add hi' hiV]
  convert! h using 1
  apply integral_congr_ae
  filter_upwards [] with x
  ring

end SK.Analytic

end
end
end
end
end
end
end

end OAI
