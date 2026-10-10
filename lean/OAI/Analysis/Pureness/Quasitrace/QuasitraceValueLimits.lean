import OAI.Analysis.Pureness.Quasitrace.QuasitracePositiveMetricContinuity
import OAI.Analysis.Pureness.Quasitrace.QuasitraceCauchy

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace UniformSpace Filter
open scoped Topology NNReal
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (hsqrt : ∀ a b : Positive D, Real.sqrt (T (Positive.add a b)) ≤ Real.sqrt (T a)+Real.sqrt (T b))
include hadd hsqrt

lemma positive_values_converge (u : ℕ → Positive D) (hu : T.IsMetricCauchy (fun k => (u k).1)) :
    ∃ v : ℝ, 0 ≤ v ∧ Tendsto (fun k => T (u k)) atTop (nhds v) := by
  let p (k : ℕ) : T.PositiveMetricPoint hadd := ⟨⟨(u k).1⟩,(u k).2⟩
  have hp : CauchySeq p := cauchySeq_iff_tendsto_dist_atTop_0.mpr hu
  have hq := (T.sqrtOnPositive_uniformContinuous hadd hsqrt).comp_cauchySeq hp
  obtain ⟨v,hv⟩ := cauchySeq_tendsto_of_complete hq
  refine ⟨v^2,sq_nonneg _,?_⟩
  have ht := hv.pow 2
  have he (k : ℕ) : T.sqrtOnPositive hadd (p k)^2 = T (u k) := Real.sq_sqrt (T.nonneg _)
  simpa only [Function.comp_apply,he] using ht

lemma positive_values_same_limit (u v : ℕ → Positive D)
    (hu : T.IsMetricCauchy (fun k => (u k).1))
    (hv : T.IsMetricCauchy (fun k => (v k).1))
    (huv : T.IsMetricNull (fun k => (u k).1-(v k).1))
    (a b : ℝ) (ha : Tendsto (fun k => T (u k)) atTop (nhds a))
    (hb : Tendsto (fun k => T (v k)) atTop (nhds b)) : a = b := by
  have hn (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ k in atTop, |Real.sqrt (T (u k))-Real.sqrt (T (v k))| < ε := by
    obtain ⟨δ,hδ,h⟩ := T.exists_metric_delta_sqrt hsqrt ε hε
    have ht := huv.eventually_lt_const hδ
    filter_upwards [ht] with k hk
    exact h (u k) (v k) hk
  have hz : Tendsto (fun k => Real.sqrt (T (u k))-Real.sqrt (T (v k))) atTop (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    simpa only [Real.dist_eq,sub_zero] using hn ε hε
  have he : Real.sqrt a-Real.sqrt b = 0 := tendsto_nhds_unique (ha.sqrt.sub hb.sqrt) hz
  obtain ⟨limitU, hlimitU, hconvergeU⟩ := T.positive_values_converge hadd hsqrt u hu
  obtain ⟨limitV, hlimitV, hconvergeV⟩ := T.positive_values_converge hadd hsqrt v hv
  have ha0 : 0 ≤ a := by simpa only [tendsto_nhds_unique hconvergeU ha] using hlimitU
  have hb0 : 0 ≤ b := by simpa only [tendsto_nhds_unique hconvergeV hb] using hlimitV
  exact (Real.sqrt_inj ha0 hb0).mp (sub_eq_zero.mp he)
end CuntzPureness.PositiveQuasitrace

end

end OAI
