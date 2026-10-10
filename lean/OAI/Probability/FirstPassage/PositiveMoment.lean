import OAI.Probability.FirstPassage.ProbabilityFoundations
import Mathlib.Probability.Independence.Integration

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal

lemma positive_weighted_density (x : ℝ) :
    exponentialPDF 1 x * ENNReal.ofReal (exp (x / 2)) =
      ENNReal.ofReal (2 : ℝ) * exponentialPDF (1 / 2) x := by
  by_cases hx : 0 ≤ x
  · rw [exponentialPDF_of_nonneg hx, exponentialPDF_of_nonneg hx]
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    simp only [one_mul]
    calc
      exp (-x) * exp (x / 2) = exp (-(1 / 2 * x)) := by
        rw [← exp_add]
        congr 1
        ring
      _ = 2 * (1 / 2 * exp (-(1 / 2 * x))) := by ring
  · rw [exponentialPDF_of_neg (lt_of_not_ge hx),
      exponentialPDF_of_neg (lt_of_not_ge hx)]
    simp

theorem exponential_moment_half :
    (∫⁻ x, ENNReal.ofReal (exp (x / 2)) ∂expMeasure 1) = 2 := by
  change (∫⁻ x, ENNReal.ofReal (exp (x / 2)) ∂volume.withDensity (exponentialPDF 1)) = _
  rw [lintegral_withDensity_eq_lintegral_mul volume (by
    unfold exponentialPDF; fun_prop) (by fun_prop)]
  simp only [Pi.mul_apply, positive_weighted_density]
  rw [lintegral_const_mul _ (by unfold exponentialPDF; fun_prop),
    lintegral_exponentialPDF_eq_one (by norm_num : (0 : ℝ) < 1 / 2), mul_one]
  norm_num

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem edge_set_positive_moment (h : ExponentialEnvironment P τ) (s : Finset Edge) :
    (∫⁻ ω : Ω, ∏ e ∈ s, ENNReal.ofReal (exp (τ e ω / 2)) ∂P) =
      2 ^ s.card := by
  have hind : iIndepFun (fun e (ω : Ω) => ENNReal.ofReal (exp (τ e ω / 2))) P :=
    h.independent.comp (fun _ (x : ℝ) => ENNReal.ofReal (exp (x / 2)))
      (by intro i; fun_prop)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun s _ hind (fun i => ((h.measurable i).div_const 2).exp.ennreal_ofReal)]
  have he : ∀ e : Edge, (∫⁻ ω : Ω, ENNReal.ofReal (exp (τ e ω / 2))
      ∂P) = 2 := by
    intro e
    rw [← lintegral_map (by fun_prop : Measurable (fun x : ℝ =>
      ENNReal.ofReal (exp (x / 2)))) (h.measurable e), h.marginal]
    exact exponential_moment_half
  simp only [he, prod_const]

omit [MeasurableSpace Ω] in
lemma positive_exp_sum (τ : Edge → Ω → ℝ) (s : Finset Edge) (ω : Ω) :
    ENNReal.ofReal (exp ((∑ e ∈ s, τ e ω) / 2)) =
      ∏ e ∈ s, ENNReal.ofReal (exp (τ e ω / 2)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert e s he ih =>
    rw [sum_insert he, prod_insert he, add_div, exp_add,
      ENNReal.ofReal_mul (exp_pos _).le, ih]

theorem costly_edge_set_probability (h : ExponentialEnvironment P τ) (s : Finset Edge) (t : ℝ) :
    P {ω : Ω | t ≤ ∑ e ∈ s, τ e ω} ≤
      2 ^ s.card / ENNReal.ofReal (exp (t / 2)) := by
  have hm := meas_ge_le_lintegral_div (μ := P)
    (f := fun ω : Ω => ENNReal.ofReal (exp ((∑ e ∈ s, τ e ω) / 2)))
    (((s.measurable_sum (fun i _ => h.measurable i)).div_const 2).exp.ennreal_ofReal.aemeasurable) (ε := ENNReal.ofReal (exp (t / 2)))
    (by positivity) ENNReal.ofReal_ne_top
  have hs : {ω : Ω | ENNReal.ofReal (exp (t / 2)) ≤
      ENNReal.ofReal (exp ((∑ e ∈ s, τ e ω) / 2))} =
      {ω : Ω | t ≤ ∑ e ∈ s, τ e ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, ENNReal.ofReal_le_ofReal_iff (exp_pos _).le,
      exp_le_exp]
    constructor <;> intro h <;> linarith
  rw [hs] at hm
  simp_rw [positive_exp_sum] at hm
  rw [edge_set_positive_moment h] at hm
  exact hm

end PlanarFPP

end OAI
