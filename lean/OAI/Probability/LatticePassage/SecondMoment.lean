import OAI.Probability.LatticePassage.NaturalMoment
import OAI.Probability.LatticePassage.EdgeInfluence
import OAI.Probability.LatticePassage.MetricCalibration
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Finset

lemma integrable_edge_square (e : Edge) :
    Integrable (fun ω : Environment => (ω e)^2) environmentLaw :=
  (measurePreserving_eval_infinitePi (fun _ : Edge => expMeasure 1) e).integrable_comp_of_integrable
    (integrable_exponential_pow 2)

lemma integral_edge_square (e : Edge) :
    (∫ ω : Environment, (ω e)^2 ∂environmentLaw) = 2 := by
  have hm := integral_map (μ := environmentLaw) (measurable_pi_apply e).aemeasurable
    (f := fun x : ℝ => x^2) (by fun_prop)
  rw [edge_marginal] at hm
  have h : (∫ x : ℝ, x^2 ∂expMeasure 1) = 2 := by simpa using integral_exponential_pow 2
  exact hm.symm.trans h

lemma edge_memLp_two (e : Edge) : MemLp (fun ω : Environment => ω e) 2 environmentLaw :=
  (memLp_two_iff_integrable_sq (measurable_pi_apply e).aestronglyMeasurable).mpr (integrable_edge_square e)

lemma integrable_edge_mul (e f : Edge) :
    Integrable (fun ω : Environment => ω e * ω f) environmentLaw :=
  (edge_memLp_two e).integrable_mul (edge_memLp_two f)

lemma integral_edge_mul (e f : Edge) :
    (∫ ω : Environment, ω e * ω f ∂environmentLaw) = 1 + if e = f then 1 else 0 := by
  classical
  by_cases he : e = f
  · subst f
    norm_num [← pow_two, integral_edge_square]
  · have h := (independent_edge_weights.indepFun he).integral_mul_eq_mul_integral
      (measurable_pi_apply e).aestronglyMeasurable (measurable_pi_apply f).aestronglyMeasurable
    simpa [Pi.mul_apply, integral_edge_weight, he] using h

theorem pathCost_memLp_two {x y : Vertex} (p : lattice.Walk x y) :
    MemLp (fun ω : Environment => pathCost ω p) 2 environmentLaw := by
  induction p with
  | nil => exact memLp_const 0
  | cons h p ih => exact (edge_memLp_two (⟨s(_,_),h⟩ : Edge)).add ih

theorem trailCost_second_moment {x y : Vertex} (p : lattice.Walk x y) (hp : p.IsTrail) :
    (∫ ω : Environment, (pathCost ω p)^2 ∂environmentLaw) =
      (p.length : ℝ) * (p.length+1) := by
  classical
  let s := (pathEdges p).toFinset
  have hc : s.card = p.length := by
    rw [List.toFinset_card_of_nodup (pathEdges_nodup hp), pathEdges_length]
  simp_rw [trailCost_eq_sum _ p hp, pow_two, sum_mul_sum]
  rw [integral_finsetSum _ (fun e _ => integrable_finsetSum _ (fun f _ => integrable_edge_mul e f))]
  simp_rw [integral_finsetSum _ (fun f _ => integrable_edge_mul _ f), integral_edge_mul]
  have he : ∀ e ∈ s, (∑ f ∈ s, (1 + if e = f then (1 : ℝ) else 0)) = s.card+1 := by
    intro e he
    simp [sum_add_distrib, he]
  change (∑ e ∈ s, ∑ f ∈ s, (1 + if e = f then (1 : ℝ) else 0)) = _
  rw [sum_congr rfl he, sum_const, nsmul_eq_mul, hc]

theorem passageTime_memLp_two (x y : Vertex) :
    MemLp (fun ω : Environment => passageTime ω x y) 2 environmentLaw := by
  obtain ⟨p,_,_⟩ := coordinate_path x y
  apply (pathCost_memLp_two p).mono' (by fun_prop)
  filter_upwards [all_edge_weights_positive] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (passageTime_nonneg ω (fun e => (hω e).le) (lattice_walk x y))]
  exact passageTime_le_pathCost ω (fun e => (hω e).le) p

theorem passageTime_second_moment (x y : Vertex) :
    (∫ ω : Environment, (passageTime ω x y)^2 ∂environmentLaw) ≤
      (latticeDistance x y : ℝ)*(latticeDistance x y+1) := by
  obtain ⟨p,hp,hl⟩ := coordinate_path x y
  apply (integral_mono_ae (passageTime_memLp_two x y).integrable_sq
    (pathCost_memLp_two p).integrable_sq (by
      filter_upwards [all_edge_weights_positive] with ω hω
      have hn := passageTime_nonneg ω (fun e => (hω e).le) (lattice_walk x y)
      have hb := passageTime_le_pathCost ω (fun e => (hω e).le) p
      nlinarith)).trans
  rw [trailCost_second_moment p hp.isTrail]
  gcongr

theorem targetCocycle_second_moment (z x y : Vertex) :
    (∫ ω : Environment, (targetCocycle z ω x y)^2 ∂environmentLaw) ≤
      (latticeDistance x y : ℝ)*(latticeDistance x y+1) := by
  have hi : MemLp (fun ω : Environment => targetCocycle z ω x y) 2 environmentLaw :=
    (passageTime_memLp_two x z).sub (passageTime_memLp_two y z)
  apply (integral_mono_ae hi.integrable_sq (passageTime_memLp_two x y).integrable_sq (by
    filter_upwards [targetCocycle_dominated] with ω hω
    have hb := hω z x y
    have hsq := pow_le_pow_left₀ (abs_nonneg _) hb 2
    simpa only [sq_abs] using hsq)).trans
    (passageTime_second_moment x y)

end CompanionFPP

end OAI
