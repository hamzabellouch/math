import OAI.Analysis.Pureness.Quasitrace.QuasitraceCauchy
import Mathlib.Analysis.CStarAlgebra.lpSpace

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)

def cauchySequenceAlgebra : StarSubalgebra ℂ (lp (fun _ : ℕ => D) ∞) where
  carrier := {u | T.IsMetricCauchy (fun k => u k)}
  zero_mem' := T.isMetricCauchy_const 0
  one_mem' := T.isMetricCauchy_const 1
  add_mem' hu hv := T.isMetricCauchy_add hadd hu hv
  mul_mem' {u v} hu hv := T.isMetricCauchy_mul hadd hu hv ‖u‖ ‖v‖ (norm_nonneg _) (norm_nonneg _)
    (lp.norm_apply_le_norm ENNReal.top_ne_zero u) (lp.norm_apply_le_norm ENNReal.top_ne_zero v)
  algebraMap_mem' c := T.isMetricCauchy_const (algebraMap ℂ D c)
  star_mem' hu := T.isMetricCauchy_star hu

omit [Nontrivial D] in
lemma isMetricCauchy_iff (u : ℕ → D) :
    T.IsMetricCauchy u ↔ @CauchySeq D ℕ (T.pseudoMetricSpace hadd).toUniformSpace _ u := by
  let := T.pseudoMetricSpace hadd
  exact (cauchySeq_iff_tendsto_dist_atTop_0 (u := u)).symm

lemma cauchySequenceAlgebra_isClosed : IsClosed (T.cauchySequenceAlgebra hadd : Set (lp (fun _ : ℕ => D) ∞)) := by
  apply isClosed_of_closure_subset
  intro u hu
  change T.IsMetricCauchy (fun k => u k)
  rw [IsMetricCauchy,Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ,hδ,hδsize⟩ := T.exists_norm_delta (ε/3) (by linarith)
  obtain ⟨v,hv,huv⟩ := Metric.mem_closure_iff.mp hu δ hδ
  have hnear (k : ℕ) : T.distance (u k) (v k) < ε/3 := by
    apply hδsize
    have hk := lp.norm_apply_le_norm ENNReal.top_ne_zero (u-v) k
    exact hk.trans_lt (by simpa only [dist_eq_norm] using huv)
  have hc : T.IsMetricCauchy (fun k => v k) := hv
  have he := (Metric.tendsto_nhds.mp hc) (ε/3) (by linarith)
  filter_upwards [he] with p hp
  have hp' : T.distance (v p.1) (v p.2) < ε/3 := by
    simpa only [Real.dist_eq,sub_zero,abs_of_nonneg (T.distance_nonneg _ _)] using hp
  have ht := T.distance_triangle hadd (u p.1) (v p.1) (u p.2)
  have ht' := T.distance_triangle hadd (v p.1) (v p.2) (u p.2)
  rw [T.distance_comm (v p.2) (u p.2)] at ht'
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (T.distance_nonneg _ _)]
  linarith [hnear p.1,hnear p.2]
end CuntzPureness.PositiveQuasitrace

end

end OAI
