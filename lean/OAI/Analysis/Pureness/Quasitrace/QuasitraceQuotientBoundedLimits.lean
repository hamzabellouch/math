import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientDensity

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))

def QuotientIsMetricCauchy (u : ℕ → T.CauchyQuotient hadd) : Prop :=
  Tendsto (fun p : ℕ × ℕ => T.quotientDistance hadd hsqrt (u p.1) (u p.2)) atTop (nhds 0)

lemma metricCauchy_of_quotient_approx (u : ℕ → T.CauchyQuotient hadd) (a : ℕ → D)
    (hu : T.QuotientIsMetricCauchy hadd hsqrt u)
    (ha : Tendsto (fun n => T.quotientDistance hadd hsqrt (T.quotientEmbedding hadd (a n)) (u n)) atTop (nhds 0)) :
    T.IsMetricCauchy a := by
  rw [IsMetricCauchy,Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨p,hp⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp hu) (ε/3) (by linarith))
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp ha) (ε/3) (by linarith))
  apply eventually_atTop.mpr
  refine ⟨(max p.1 N,max p.2 N),fun q hq => ?_⟩
  have h1 := hN q.1 ((le_max_right _ _).trans hq.1)
  have h2 := hp q ⟨(le_max_left _ _).trans hq.1,(le_max_left _ _).trans hq.2⟩
  have h3 := hN q.2 ((le_max_right _ _).trans hq.2)
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (T.quotientDistance_nonneg hadd hsqrt _ _)] at h1 h2 h3
  have ht := T.quotientDistance_triangle hadd hsqrt (T.quotientEmbedding hadd (a q.1)) (u q.1)
    (T.quotientEmbedding hadd (a q.2))
  have ht' := T.quotientDistance_triangle hadd hsqrt (u q.1) (u q.2) (T.quotientEmbedding hadd (a q.2))
  rw [T.quotientDistance_embedding] at ht
  rw [T.quotientDistance_comm hadd hsqrt (u q.2)] at ht'
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (T.distance_nonneg _ _)]
  linarith

lemma quotient_bounded_metric_limit_with_slack (u : ℕ → T.CauchyQuotient hadd)
    (hu : T.QuotientIsMetricCauchy hadd hsqrt u) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n, ‖u n‖ ≤ C)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x : T.CauchyQuotient hadd, ‖x‖ ≤ C+ε ∧
      Tendsto (fun n => T.quotientDistance hadd hsqrt (u n) x) atTop (nhds 0) := by
  have hex (n : ℕ) := T.exists_quotient_metric_approx hadd hsqrt (u n) hε
    (show 0 < 1/((n:ℝ)+1) by positivity)
  choose a han had using hex
  have ha : Tendsto (fun n => T.quotientDistance hadd hsqrt (T.quotientEmbedding hadd (a n)) (u n)) atTop (nhds 0) :=
    squeeze_zero (fun n => T.quotientDistance_nonneg hadd hsqrt _ _) (fun n => (had n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hac := T.metricCauchy_of_quotient_approx hadd hsqrt u a hu ha
  have hab (n : ℕ) : ‖a n‖ ≤ C+ε := by linarith [han n,hb n]
  let v : T.cauchySequenceAlgebra hadd :=
    ⟨⟨a,memℓp_infty ⟨C+ε,by rintro _ ⟨n,rfl⟩; exact hab n⟩⟩,hac⟩
  refine ⟨T.cauchyQuotientMap hadd v,?_,?_⟩
  · exact (T.cauchyQuotientMap_norm_le hadd v).trans
      (lp.norm_le_of_forall_le (by linarith : 0 ≤ C+ε) hab)
  · have hv := T.quotientEmbedding_representative_tendsto hadd hsqrt v
    apply squeeze_zero (fun n => T.quotientDistance_nonneg hadd hsqrt _ _)
      (fun n => (T.quotientDistance_triangle hadd hsqrt (u n) (T.quotientEmbedding hadd (a n)) _))
    have ha' : Tendsto (fun n => T.quotientDistance hadd hsqrt (u n) (T.quotientEmbedding hadd (a n))) atTop (nhds 0) := by
      simpa only [T.quotientDistance_comm hadd hsqrt] using ha
    simpa using ha'.add hv

lemma quotient_metric_limit_unique (u : ℕ → T.CauchyQuotient hadd) (x y : T.CauchyQuotient hadd)
    (hx : Tendsto (fun n => T.quotientDistance hadd hsqrt (u n) x) atTop (nhds 0))
    (hy : Tendsto (fun n => T.quotientDistance hadd hsqrt (u n) y) atTop (nhds 0)) : x = y := by
  apply (T.quotientDistance_eq_zero_iff hadd hsqrt x y).mp
  apply le_antisymm _ (T.quotientDistance_nonneg hadd hsqrt x y)
  have h : ∀ n, T.quotientDistance hadd hsqrt x y ≤
      T.quotientDistance hadd hsqrt (u n) x+T.quotientDistance hadd hsqrt (u n) y := by
    intro n
    simpa only [T.quotientDistance_comm hadd hsqrt x] using T.quotientDistance_triangle hadd hsqrt x (u n) y
  exact ge_of_tendsto (show Tendsto (fun n => T.quotientDistance hadd hsqrt (u n) x+
    T.quotientDistance hadd hsqrt (u n) y) atTop (nhds 0) by simpa using hx.add hy) (Eventually.of_forall h)

lemma quotient_bounded_metric_limit (u : ℕ → T.CauchyQuotient hadd)
    (hu : T.QuotientIsMetricCauchy hadd hsqrt u) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n, ‖u n‖ ≤ C) :
    ∃ x : T.CauchyQuotient hadd, ‖x‖ ≤ C ∧
      Tendsto (fun n => T.quotientDistance hadd hsqrt (u n) x) atTop (nhds 0) := by
  obtain ⟨x,_,hx⟩ := T.quotient_bounded_metric_limit_with_slack hadd hsqrt u hu C hC hb (by norm_num : (0:ℝ) < 1)
  refine ⟨x,?_,hx⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨y,hy,hyt⟩ := T.quotient_bounded_metric_limit_with_slack hadd hsqrt u hu C hC hb hε
  rw [T.quotient_metric_limit_unique hadd hsqrt u x y hx hyt]
  exact hy
end CuntzPureness.PositiveQuasitrace

end

end OAI
