import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientMetricLimits

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal ComplexOrder
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

lemma exists_quotient_value_metric_approx (x : T.CauchyQuotient hadd) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ a : D, ‖a‖ < ‖x‖+ε ∧ T.quotientDistance hadd hsqrt (T.quotientEmbedding hadd a) x < δ ∧
      ‖T.complexValue a-T.quotientValue hadd hsqrt x‖ < δ := by
  obtain ⟨u,rfl,hu⟩ := T.cauchyQuotient_norm_lt_rep hadd x hε
  have ht := T.quotientEmbedding_representative_tendsto hadd hsqrt u
  have hv := T.cauchyValue_tendsto hadd hsqrt u
  rw [← T.quotientValue_map hadd hsqrt u] at hv
  obtain ⟨k,hk,hkv⟩ := (((Metric.tendsto_nhds.mp ht) δ hδ).and
    ((Metric.tendsto_nhds.mp hv) δ hδ)).exists
  refine ⟨u.1 k,(lp.norm_apply_le_norm ENNReal.top_ne_zero u.1 k).trans_lt hu,?_,?_⟩
  · simpa only [Real.dist_eq,sub_zero,abs_of_nonneg (T.quotientDistance_nonneg hadd hsqrt _ _)] using hk
  · simpa only [dist_eq_norm] using hkv

lemma quotientValue_bounded_metric_limit {u : ℕ → T.CauchyQuotient hadd} {x : T.CauchyQuotient hadd}
    (hu : Tendsto (fun n => T.quotientDistance hadd hsqrt (u n) x) atTop (nhds 0))
    (C : ℝ) (_hC : 0 ≤ C) (hb : ∀ n, ‖u n‖ ≤ C) :
    Tendsto (fun n => T.quotientValue hadd hsqrt (u n)) atTop (nhds (T.quotientValue hadd hsqrt x)) := by
  have hex (n : ℕ) := T.exists_quotient_value_metric_approx hadd hsqrt (u n)
    (by norm_num : (0:ℝ)<1) (show 0 < 1/((n:ℝ)+1) by positivity)
  choose a han had hav using hex
  have ha : Tendsto (fun n => T.quotientDistance hadd hsqrt (T.quotientEmbedding hadd (a n)) (u n)) atTop (nhds 0) :=
    squeeze_zero (fun n => T.quotientDistance_nonneg hadd hsqrt _ _) (fun n => (had n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hax : Tendsto (fun n => T.quotientDistance hadd hsqrt (T.quotientEmbedding hadd (a n)) x) atTop (nhds 0) := by
    apply squeeze_zero (fun n => T.quotientDistance_nonneg hadd hsqrt _ _)
      (fun n => T.quotientDistance_triangle hadd hsqrt _ (u n) x)
    simpa only [add_zero] using ha.add hu
  have hac : T.IsMetricCauchy a := by
    apply T.metricCauchy_of_quotient_approx hadd hsqrt (fun _ => x) a _ hax
    simp only [QuotientIsMetricCauchy,T.quotientDistance_self]
    exact tendsto_const_nhds
  have hab (n : ℕ) : ‖a n‖ ≤ C+1 := by linarith [han n,hb n]
  let v : T.cauchySequenceAlgebra hadd :=
    ⟨⟨a,memℓp_infty ⟨C+1,by rintro _ ⟨n,rfl⟩; exact hab n⟩⟩,hac⟩
  have hvx : T.cauchyQuotientMap hadd v=x := T.quotient_metric_limit_unique hadd hsqrt _ _ _
    (T.quotientEmbedding_representative_tendsto hadd hsqrt v) hax
  have hval := T.cauchyValue_tendsto hadd hsqrt v
  rw [← T.quotientValue_map hadd hsqrt v,hvx] at hval
  have hdiff : Tendsto (fun n => T.complexValue (a n)-T.quotientValue hadd hsqrt (u n)) atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hav n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  change Tendsto (fun n => T.complexValue (a n)) atTop (nhds (T.quotientValue hadd hsqrt x)) at hval
  have he := hval.sub hdiff
  simpa only [sub_sub_cancel,sub_zero] using he
end CuntzPureness.PositiveQuasitrace

end

end OAI
