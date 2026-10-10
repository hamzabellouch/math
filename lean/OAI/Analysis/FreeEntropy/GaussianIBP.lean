import OAI.Analysis.FreeEntropy.Basic

namespace OAI

universe u1

noncomputable section
open scoped ENNReal NNReal Polynomial
open MeasureTheory ProbabilityTheory Filter
namespace FiniteEntropySeparation
 theorem gaussian_weight_integrable {E : Type u1} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) {f : ℝ → E} :
    Integrable f (gaussianReal μ v) ↔ Integrable (fun x => gaussianPDFReal μ v x • f x) := by
  rw [gaussianReal_of_var_ne_zero _ hv]
  simpa only [toReal_gaussianPDF] using integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF μ v) (Filter.Eventually.of_forall (fun _ => gaussianPDF_lt_top))
 theorem hasDerivAt_gaussianPDFReal (μ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal μ v) (-(x-μ)/(v : ℝ) * gaussianPDFReal μ v x) x := by
  have hv' : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  have hd := (hasDerivAt_const x (1 / Real.sqrt (2*Real.pi*(v : ℝ)))).mul
    (((((hasDerivAt_id x).sub_const μ).pow 2).neg.div_const (2*(v : ℝ))).exp)
  have he := hd.congr_deriv (show _ = -(x-μ)/(v : ℝ) * gaussianPDFReal μ v x by
    unfold gaussianPDFReal
    dsimp
    field_simp
    ring)
  convert he using 1
  try rfl
  funext y
  simp [gaussianPDFReal, one_div]

 theorem gaussian_integrationByParts {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hi : Integrable f (gaussianReal μ v)) (hi' : Integrable f' (gaussianReal μ v))
    (hx : Integrable (fun x => (x-μ)*f x) (gaussianReal μ v)) :
    (∫ x, (x-μ)*f x ∂gaussianReal μ v) = (v : ℝ) * ∫ x, f' x ∂gaussianReal μ v := by
  have h0 := (gaussian_weight_integrable hv).mp hi
  have h1 := (gaussian_weight_integrable hv).mp hi'
  have h2 := ((gaussian_weight_integrable hv).mp hx).const_mul (-(v : ℝ)⁻¹)
  have h2' : Integrable (fun x => f x * (-(x-μ)/(v : ℝ) * gaussianPDFReal μ v x)) := by
    convert h2 using 1
    ext x
    simp only [smul_eq_mul, div_eq_mul_inv]
    ring
  have h1' : Integrable (fun x => f' x * gaussianPDFReal μ v x) := by
    simpa only [smul_eq_mul, mul_comm] using h1
  have h0' : Integrable (fun x => f x * gaussianPDFReal μ v x) := by
    simpa only [smul_eq_mul, mul_comm] using h0
  have he := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => hf x) (fun x _ => hasDerivAt_gaussianPDFReal μ v hv x) h2' h1' h0'
  have heq : (fun x => f x * (-(x-μ)/(v : ℝ) * gaussianPDFReal μ v x)) =
      fun x => -(v : ℝ)⁻¹ * (gaussianPDFReal μ v x * ((x-μ)*f x)) := by
    funext x; simp only [div_eq_mul_inv]; ring
  rw [heq, integral_const_mul] at he
  simp_rw [mul_comm (f' _) (gaussianPDFReal μ v _)] at he
  rw [integral_gaussianReal_eq_integral_smul hv, integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  have hv' : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  have hh := congrArg ((v : ℝ) * ·) he
  field_simp at hh
  simp only [mul_assoc] at hh
  linarith
 theorem gaussian_pow_integrable (μ : ℝ) (v : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ => x^n) (gaussianReal μ v) := by
  by_cases hn : n = 0
  · subst n; simp
  have h := (memLp_id_gaussianReal' (μ := μ) (v := v) (n : ℝ≥0∞) (by simp)).integrable_norm_pow hn
  apply h.mono' (by fun_prop)
  exact Filter.Eventually.of_forall (fun x => by simp [norm_pow])
 theorem gaussian_polynomial_integrable (μ : ℝ) (v : ℝ≥0) (P : ℝ[X]) :
    Integrable (fun x => P.eval x) (gaussianReal μ v) := by
  classical
  simp only [Polynomial.eval_eq_sum_range]
  exact integrable_finsetSum _ (fun i _ => (gaussian_pow_integrable μ v i).const_mul _)
 theorem gaussian_polynomial_stein (P : ℝ[X]) :
    (∫ x, x*P.eval x ∂gaussianReal 0 1) = ∫ x, P.derivative.eval x ∂gaussianReal 0 1 := by
  have hi := gaussian_polynomial_integrable 0 1 (Polynomial.X * P)
  simpa only [sub_zero, NNReal.coe_one, one_mul] using gaussian_integrationByParts (by norm_num : (1 : ℝ≥0) ≠ 0)
    (fun x => P.hasDerivAt x) (gaussian_polynomial_integrable 0 1 P)
    (gaussian_polynomial_integrable 0 1 P.derivative) (by simpa using hi)
end FiniteEntropySeparation

end

end OAI
