import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientMetric

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

lemma quotientEmbedding_representative_tendsto (u : T.cauchySequenceAlgebra hadd) :
    Tendsto (fun k => T.quotientDistance hadd hsqrt
      (T.quotientEmbedding hadd (u.1 k)) (T.cauchyQuotientMap hadd u)) atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have he := (Metric.tendsto_nhds.mp u.2) (ε/2) (half_pos hε)
  obtain ⟨p,hp⟩ := eventually_atTop.mp he
  let N := max p.1 p.2
  apply eventually_atTop.mpr
  refine ⟨N,fun i hi => ?_⟩
  have hb : T.quotientDistance hadd hsqrt (T.quotientEmbedding hadd (u.1 i))
      (T.cauchyQuotientMap hadd u) ≤ ε/2 := by
    apply le_of_tendsto (T.quotientDistance_map_tendsto hadd hsqrt (T.constantCauchy hadd (u.1 i)) u)
    apply eventually_atTop.mpr
    refine ⟨N,fun j hj => ?_⟩
    have hij := hp (i,j) ⟨(le_max_left _ _).trans hi,(le_max_right _ _).trans hj⟩
    have hij' : T.distance (u.1 i) (u.1 j) < ε/2 := by
      simpa only [Real.dist_eq,sub_zero,abs_of_nonneg (T.distance_nonneg _ _)] using hij
    exact hij'.le
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (T.quotientDistance_nonneg hadd hsqrt _ _)]
  linarith

lemma exists_quotient_metric_approx (x : T.CauchyQuotient hadd) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ a : D, ‖a‖ < ‖x‖+ε ∧ T.quotientDistance hadd hsqrt (T.quotientEmbedding hadd a) x < δ := by
  obtain ⟨u,rfl,hu⟩ := T.cauchyQuotient_norm_lt_rep hadd x hε
  have ht := T.quotientEmbedding_representative_tendsto hadd hsqrt u
  obtain ⟨k,hk⟩ := ((Metric.tendsto_nhds.mp ht) δ hδ).exists
  refine ⟨u.1 k,(lp.norm_apply_le_norm ENNReal.top_ne_zero u.1 k).trans_lt hu,?_⟩
  simpa only [Real.dist_eq,sub_zero,abs_of_nonneg (T.quotientDistance_nonneg hadd hsqrt _ _)] using hk
end CuntzPureness.PositiveQuasitrace

end

end OAI
