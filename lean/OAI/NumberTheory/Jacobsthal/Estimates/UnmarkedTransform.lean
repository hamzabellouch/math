import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import OAI.NumberTheory.Jacobsthal.Sieve.MarkedCycleFactorization

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
open NumberTheoryLean.CostReturnLaw

lemma unmarked_mass_lt_one : unmarkedCostLaw univ < 1 := by
  have he := congrArg (fun μ : Measure ℝ => μ univ) markedCostLaw_add_unmarked
  have hsum : unmarkedCostLaw univ+markProbability=1 := by
    simpa only [Measure.add_apply,markedCostLaw_mass,measure_univ,add_comm] using he
  exact (ENNReal.lt_add_right (measure_ne_top _ _) markProbability_pos.ne').trans_eq hsum

lemma positive_cost_of_lower {G : ℝ} (hG : Real.log (4/3) ≤ G) : 0 ≤ G := by
  have h : 0 < Real.log (4/3:ℝ) := Real.log_pos (by norm_num)
  linarith

theorem exists_subcritical_unmarked_transform : ∃ eta : ℝ, 0 < eta ∧
    (∫⁻ G, ENNReal.ofReal (Real.exp (eta*G)) ∂unmarkedCostLaw) < 1 ∧
    (∫⁻ G, ENNReal.ofReal (Real.exp (eta*G)) ∂markedCostLaw) < ∞ := by
  obtain ⟨eta0,heta0,hMarked,hUnmarked⟩ := source_marked_exponential_moments
  let eta : ℕ → ℝ := fun n => eta0/((n:ℝ)+1)
  have heta (n : ℕ) : 0 < eta n := by dsimp [eta]; positivity
  have hle (n : ℕ) : eta n ≤ eta0 := by
    exact div_le_self heta0.le (by have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  have hseq : Tendsto eta atTop (𝓝 0) := by
    simpa only [eta,mul_one_div,mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul eta0
  let F : ℕ → ℝ → ℝ≥0∞ := fun n G => ENNReal.ofReal (Real.exp (eta n*G))
  let bound : ℝ → ℝ≥0∞ := fun G => ENNReal.ofReal (Real.exp (eta0*G))
  have hF (n : ℕ) : Measurable (F n) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul measurable_id))
  have hBound (n : ℕ) : F n ≤ᵐ[unmarkedCostLaw] bound := by
    filter_upwards [source_unmarked_cost_lower] with G hG
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (hle n) (positive_cost_of_lower hG)))
  have hLim : ∀ᵐ G ∂unmarkedCostLaw, Tendsto (fun n => F n G) atTop (𝓝 1) := by
    apply Eventually.of_forall
    intro G
    have he := (ENNReal.continuous_ofReal.tendsto _).comp
      ((Real.continuous_exp.tendsto _).comp (hseq.mul_const G))
    simpa only [F,Function.comp_def,zero_mul,Real.exp_zero,ENNReal.ofReal_one] using! he
  have hInt := tendsto_lintegral_of_dominated_convergence bound hF hBound hUnmarked.ne hLim
  have hInt' : Tendsto (fun n => ∫⁻ G, F n G ∂unmarkedCostLaw) atTop
      (𝓝 (unmarkedCostLaw univ)) := by simpa only [lintegral_one] using hInt
  obtain ⟨n,hn⟩ := (hInt'.eventually (gt_mem_nhds unmarked_mass_lt_one)).exists
  refine ⟨eta n,heta n,hn,?_⟩
  have hm : (∫⁻ G, ENNReal.ofReal (Real.exp (eta n*G)) ∂markedCostLaw) ≤
      ∫⁻ G, ENNReal.ofReal (Real.exp (eta0*G)) ∂markedCostLaw := by
    apply lintegral_mono_ae
    filter_upwards [source_marked_cost_lower] with G hG
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (hle n) (positive_cost_of_lower hG)))
  exact hm.trans_lt hMarked

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
