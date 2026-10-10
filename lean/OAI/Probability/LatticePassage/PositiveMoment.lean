import OAI.Probability.LatticePassage.CheapPath

namespace OAI

namespace CompanionFPP
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

theorem edge_set_positive_moment (s : Finset Edge) :
    (∫⁻ ω : Environment, ∏ e ∈ s, ENNReal.ofReal (exp (ω e / 2)) ∂environmentLaw) =
      2 ^ s.card := by
  have hind : iIndepFun (fun e (ω : Environment) => ENNReal.ofReal (exp (ω e / 2)))
      environmentLaw := iIndepFun_infinitePi (X := fun _ (x : ℝ) =>
        ENNReal.ofReal (exp (x / 2))) (by intro i; fun_prop)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun s _ hind (by intro i; fun_prop)]
  have he : ∀ e : Edge, (∫⁻ ω : Environment, ENNReal.ofReal (exp (ω e / 2))
      ∂environmentLaw) = 2 := by
    intro e
    rw [← lintegral_map (by fun_prop : Measurable (fun x : ℝ =>
      ENNReal.ofReal (exp (x / 2)))) (measurable_pi_apply e), edge_marginal]
    exact exponential_moment_half
  simp only [he, prod_const]

lemma positive_exp_sum (s : Finset Edge) (ω : Environment) :
    ENNReal.ofReal (exp ((∑ e ∈ s, ω e) / 2)) =
      ∏ e ∈ s, ENNReal.ofReal (exp (ω e / 2)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert e s he ih =>
    rw [sum_insert he, prod_insert he, add_div, exp_add,
      ENNReal.ofReal_mul (exp_pos _).le, ih]

theorem costly_edge_set_probability (s : Finset Edge) (t : ℝ) :
    environmentLaw {ω : Environment | t ≤ ∑ e ∈ s, ω e} ≤
      2 ^ s.card / ENNReal.ofReal (exp (t / 2)) := by
  have hm := meas_ge_le_lintegral_div (μ := environmentLaw)
    (f := fun ω : Environment => ENNReal.ofReal (exp ((∑ e ∈ s, ω e) / 2)))
    (by fun_prop) (ε := ENNReal.ofReal (exp (t / 2)))
    (by positivity) ENNReal.ofReal_ne_top
  have hs : {ω : Environment | ENNReal.ofReal (exp (t / 2)) ≤
      ENNReal.ofReal (exp ((∑ e ∈ s, ω e) / 2))} =
      {ω : Environment | t ≤ ∑ e ∈ s, ω e} := by
    ext ω
    simp only [Set.mem_ofPred_eq, ENNReal.ofReal_le_ofReal_iff (exp_pos _).le,
      exp_le_exp]
    constructor <;> intro h <;> linarith
  rw [hs] at hm
  simp_rw [positive_exp_sum] at hm
  rw [edge_set_positive_moment] at hm
  exact hm

theorem costly_trail_probability {x y : Vertex} (p : lattice.Walk x y)
    (hp : p.IsTrail) (t : ℝ) :
    environmentLaw.real {ω : Environment | t ≤ pathCost ω p} ≤
      (2 : ℝ)^p.length * exp (-t / 2) := by
  classical
  have hn := pathEdges_nodup hp
  have hc : (pathEdges p).toFinset.card = p.length := by
    rw [List.toFinset_card_of_nodup hn, pathEdges_length]
  have he : ∀ ω : Environment, (∑ e ∈ (pathEdges p).toFinset, ω e) = pathCost ω p := by
    intro ω
    rw [pathCost_eq_edgeList_sum]
    exact List.sum_toFinset _ hn
  have h := costly_edge_set_probability (pathEdges p).toFinset t
  simp only [he, hc] at h
  have hr := ENNReal.toReal_mono (show (2 : ℝ≥0∞)^p.length /
      ENNReal.ofReal (exp (t/2)) ≠ ⊤ from
      ENNReal.div_ne_top (by simp) (by positivity)) h
  simp only [ENNReal.toReal_div, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (exp_pos _).le, ENNReal.toReal_ofNat] at hr
  change environmentLaw.real _ ≤ _ at hr
  rw [show -t / 2 = -(t / 2) by ring, exp_neg]
  simpa only [div_eq_mul_inv] using hr

end CompanionFPP

end OAI
