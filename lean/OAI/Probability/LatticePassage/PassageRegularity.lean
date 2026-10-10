import OAI.Probability.LatticePassage.GeodesicTail
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

@[fun_prop] theorem measurable_pathCost {x y : Vertex} (p : lattice.Walk x y) :
    Measurable (fun ω : Environment => pathCost ω p) := by
  induction p with
  | nil => exact measurable_const
  | cons h p ih => exact (measurable_pi_apply _).add ih

instance countable_lattice_walk (x y : Vertex) : Countable (lattice.Walk x y) :=
  Function.Injective.countable (f := fun p : lattice.Walk x y => p.support)
    (fun _ _ h => SimpleGraph.Walk.ext_support h)

@[fun_prop] theorem measurable_passageTime (x y : Vertex) :
    Measurable (fun ω : Environment => passageTime ω x y) := by
  exact Measurable.iInf (fun p : lattice.Walk x y => measurable_pathCost p)

theorem trail_positive_moment {x y : Vertex} (p : lattice.Walk x y) (hp : p.IsTrail) :
    (∫⁻ ω : Environment, ENNReal.ofReal (exp (pathCost ω p / 2)) ∂environmentLaw) =
      2 ^ p.length := by
  classical
  have hn := pathEdges_nodup hp
  have hc : (pathEdges p).toFinset.card = p.length := by
    rw [List.toFinset_card_of_nodup hn, pathEdges_length]
  have he : ∀ ω : Environment, (∑ e ∈ (pathEdges p).toFinset, ω e) = pathCost ω p := by
    intro ω
    rw [pathCost_eq_edgeList_sum]
    exact List.sum_toFinset _ hn
  have h := edge_set_positive_moment (pathEdges p).toFinset
  simp_rw [← positive_exp_sum, he, hc] at h
  exact h

theorem passageTime_positive_moment (x y : Vertex) :
    (∫⁻ ω : Environment, ENNReal.ofReal (exp (passageTime ω x y / 2)) ∂environmentLaw) ≤
      2 ^ latticeDistance x y := by
  obtain ⟨p,hp,hl⟩ := coordinate_path x y
  calc
    _ ≤ ∫⁻ ω : Environment, ENNReal.ofReal (exp (pathCost ω p / 2)) ∂environmentLaw := by
      apply lintegral_mono_ae
      filter_upwards [all_edge_weights_positive] with ω hω
      apply ENNReal.ofReal_le_ofReal
      apply exp_le_exp.mpr
      exact div_le_div_of_nonneg_right (passageTime_le_pathCost ω (fun e => (hω e).le) p)
        (by norm_num)
    _ = 2 ^ p.length := trail_positive_moment p hp.isTrail
    _ ≤ _ := by gcongr; norm_num

theorem integrable_exp_passageTime (x y : Vertex) :
    Integrable (fun ω : Environment => exp (passageTime ω x y / 2)) environmentLaw := by
  apply (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
    (by filter_upwards [] with ω; positivity)).mp
  exact ne_of_lt ((passageTime_positive_moment x y).trans_lt (by finiteness))

theorem integrable_passageTime (x y : Vertex) :
    Integrable (fun ω : Environment => passageTime ω x y) environmentLaw := by
  apply ((integrable_exp_passageTime x y).const_mul 2).mono'
    (measurable_passageTime x y).aestronglyMeasurable
  filter_upwards [all_edge_weights_positive] with ω hω
  have hn := passageTime_nonneg ω (fun e => (hω e).le) (lattice_walk x y)
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  have he := add_one_le_exp (passageTime ω x y / 2)
  linarith

theorem passageTime_upper_tail (x y : Vertex) (t : ℝ) :
    environmentLaw.real {ω : Environment | t ≤ passageTime ω x y} ≤
      (2 : ℝ)^latticeDistance x y * exp (-t/2) := by
  obtain ⟨p,hp,hl⟩ := coordinate_path x y
  have hsub : environmentLaw {ω : Environment | t ≤ passageTime ω x y} ≤
      environmentLaw {ω : Environment | t ≤ pathCost ω p} := by
    apply measure_mono_ae
    filter_upwards [all_edge_weights_positive] with ω hω
    intro ht
    exact ht.trans (passageTime_le_pathCost ω (fun e => (hω e).le) p)
  apply (ENNReal.toReal_mono (measure_ne_top _ _) hsub).trans
  apply (costly_trail_probability p hp.isTrail t).trans
  gcongr
  norm_num

end CompanionFPP

end OAI
