import OAI.Probability.LatticePassage.Environment
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal

lemma weighted_exponential_density (x : ℝ) :
    exponentialPDF 1 x * ENNReal.ofReal (exp (-5 * x)) =
      ENNReal.ofReal (1 / 6 : ℝ) * exponentialPDF 6 x := by
  by_cases hx : 0 ≤ x
  · rw [exponentialPDF_of_nonneg hx, exponentialPDF_of_nonneg hx]
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    simp only [one_mul]
    calc
      exp (-x) * exp (-5 * x) = exp (-(6 * x)) := by
        rw [← exp_add]
        congr 1
        ring
      _ = (1 / 6 : ℝ) * (6 * exp (-(6 * x))) := by ring
  · rw [exponentialPDF_of_neg (lt_of_not_ge hx),
      exponentialPDF_of_neg (lt_of_not_ge hx)]
    simp

theorem exponential_laplace_five :
    (∫⁻ x, ENNReal.ofReal (exp (-5 * x)) ∂expMeasure 1) = ENNReal.ofReal (1 / 6 : ℝ) := by
  change (∫⁻ x, ENNReal.ofReal (exp (-5 * x)) ∂volume.withDensity (exponentialPDF 1)) = _
  rw [lintegral_withDensity_eq_lintegral_mul volume (by
    unfold exponentialPDF; fun_prop) (by fun_prop)]
  simp only [Pi.mul_apply, weighted_exponential_density]
  rw [lintegral_const_mul _ (by unfold exponentialPDF; fun_prop),
    lintegral_exponentialPDF_eq_one (by norm_num : (0 : ℝ) < 6), mul_one]

theorem edge_set_laplace (s : Finset Edge) :
    (∫⁻ ω : Environment, ∏ e ∈ s, ENNReal.ofReal (exp (-5 * ω e)) ∂environmentLaw) =
      ENNReal.ofReal (1 / 6 : ℝ) ^ s.card := by
  have hind : iIndepFun (fun e (ω : Environment) => ENNReal.ofReal (exp (-5 * ω e)))
      environmentLaw := iIndepFun_infinitePi (X := fun _ (x : ℝ) =>
        ENNReal.ofReal (exp (-5 * x))) (by intro i; fun_prop)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun s _ hind (by intro i; fun_prop)]
  have he : ∀ e : Edge, (∫⁻ ω : Environment, ENNReal.ofReal (exp (-5 * ω e))
      ∂environmentLaw) = ENNReal.ofReal (1 / 6 : ℝ) := by
    intro e
    rw [← lintegral_map (by fun_prop : Measurable (fun x : ℝ =>
      ENNReal.ofReal (exp (-5 * x)))) (measurable_pi_apply e), edge_marginal]
    exact exponential_laplace_five
  simp only [he, prod_const]

lemma edge_set_exp_sum (s : Finset Edge) (ω : Environment) :
    ENNReal.ofReal (exp (-5 * ∑ e ∈ s, ω e)) =
      ∏ e ∈ s, ENNReal.ofReal (exp (-5 * ω e)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert e s he ih =>
    rw [sum_insert he, prod_insert he, mul_add, exp_add,
      ENNReal.ofReal_mul (exp_pos _).le, ih]

theorem edge_set_sum_laplace (s : Finset Edge) :
    (∫⁻ ω : Environment, ENNReal.ofReal (exp (-5 * ∑ e ∈ s, ω e)) ∂environmentLaw) =
      ENNReal.ofReal (1 / 6 : ℝ) ^ s.card := by
  simp_rw [edge_set_exp_sum]
  exact edge_set_laplace s

theorem cheap_edge_set_probability (s : Finset Edge) (t : ℝ) :
    environmentLaw {ω : Environment | (∑ e ∈ s, ω e) ≤ t} ≤
      ENNReal.ofReal (1 / 6 : ℝ) ^ s.card / ENNReal.ofReal (exp (-5 * t)) := by
  have hm := meas_ge_le_lintegral_div (μ := environmentLaw)
    (f := fun ω : Environment => ENNReal.ofReal (exp (-5 * ∑ e ∈ s, ω e)))
    (by fun_prop) (ε := ENNReal.ofReal (exp (-5 * t)))
    (by positivity) ENNReal.ofReal_ne_top
  have hs : {ω : Environment | ENNReal.ofReal (exp (-5 * t)) ≤
      ENNReal.ofReal (exp (-5 * ∑ e ∈ s, ω e))} =
      {ω : Environment | (∑ e ∈ s, ω e) ≤ t} := by
    ext ω
    simp only [Set.mem_ofPred_eq, ENNReal.ofReal_le_ofReal_iff (exp_pos _).le,
      exp_le_exp]
    constructor <;> intro h <;> linarith
  rw [hs, edge_set_sum_laplace] at hm
  exact hm

end CompanionFPP

end OAI
