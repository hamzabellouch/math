import OAI.Probability.LatticePassage.LocalizationMean

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real

lemma exponential_nat_moment_density (n : ℕ) (x : ℝ) :
    exponentialPDF 1 x * ENNReal.ofReal (x^n) =
      ENNReal.ofReal (n.factorial : ℝ) * gammaPDF (n+1) 1 x := by
  by_cases hx : 0 ≤ x
  · rw [exponentialPDF_of_nonneg hx, gammaPDF_of_nonneg hx,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [one_mul, one_rpow, add_sub_cancel_right]
    rw [Real.rpow_natCast]
    rw [Real.Gamma_nat_eq_factorial]
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  · rw [exponentialPDF_of_neg (lt_of_not_ge hx), gammaPDF_of_neg (lt_of_not_ge hx)]
    simp

theorem exponential_nat_lmoment (n : ℕ) :
    (∫⁻ x, ENNReal.ofReal (x^n) ∂expMeasure 1) = n.factorial := by
  change (∫⁻ x, ENNReal.ofReal (x^n) ∂volume.withDensity (exponentialPDF 1)) = _
  rw [lintegral_withDensity_eq_lintegral_mul volume (by unfold exponentialPDF; fun_prop)
    (by fun_prop)]
  simp only [Pi.mul_apply, exponential_nat_moment_density]
  rw [lintegral_const_mul _ (by unfold gammaPDF; fun_prop),
    lintegral_gammaPDF_eq_one (by positivity) (by norm_num), mul_one]
  simp

theorem integrable_exponential_pow (n : ℕ) :
    Integrable (fun x : ℝ => x^n) (expMeasure 1) := by
  apply (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
    (by filter_upwards [exponential_positive] with x hx; positivity)).mp
  rw [exponential_nat_lmoment]
  finiteness

theorem integral_exponential_pow (n : ℕ) :
    (∫ x : ℝ, x^n ∂expMeasure 1) = n.factorial := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (by filter_upwards [exponential_positive] with x hx; positivity) (by fun_prop),
    exponential_nat_lmoment]
  simp

lemma integrable_edge_weight (e : Edge) :
    Integrable (fun ω : Environment => ω e) environmentLaw := by
  have h := (integrable_exponential_pow 1)
  simp only [pow_one] at h
  exact (measurePreserving_eval_infinitePi (fun _ : Edge => expMeasure 1) e).integrable_comp_of_integrable h

lemma integral_edge_weight (e : Edge) :
    (∫ ω : Environment, ω e ∂environmentLaw) = 1 := by
  have h := integral_map (μ := environmentLaw) (measurable_pi_apply e).aemeasurable
    (f := fun x : ℝ => x) (by fun_prop)
  rw [edge_marginal] at h
  have h1 : (∫ x : ℝ, x ∂expMeasure 1) = 1 := by
    simpa using integral_exponential_pow 1
  exact h.symm.trans h1

theorem integral_pathCost {x y : Vertex} (p : lattice.Walk x y) :
    Integrable (fun ω : Environment => pathCost ω p) environmentLaw ∧
      (∫ ω : Environment, pathCost ω p ∂environmentLaw) = p.length := by
  induction p with
  | nil => simp [pathCost_nil]
  | cons h p ih =>
    have he := integrable_edge_weight (⟨s(_, _), h⟩ : Edge)
    constructor
    · exact he.add ih.1
    · rw [show (fun ω : Environment => pathCost ω (.cons h p)) =
        (fun ω => ω (⟨s(_, _), h⟩ : Edge) + pathCost ω p) from rfl,
        integral_add he ih.1, integral_edge_weight, ih.2]
      simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
      ring

theorem mean_passageTime_le_distance (x y : Vertex) :
    (∫ ω : Environment, passageTime ω x y ∂environmentLaw) ≤ latticeDistance x y := by
  obtain ⟨p,hp,hl⟩ := coordinate_path x y
  have h := integral_mono_ae (integrable_passageTime x y) (integral_pathCost p).1
    (by filter_upwards [all_edge_weights_positive] with ω hω
        exact passageTime_le_pathCost ω (fun e => (hω e).le) p)
  rw [(integral_pathCost p).2] at h
  exact h.trans (by exact_mod_cast hl)

end CompanionFPP

end OAI
