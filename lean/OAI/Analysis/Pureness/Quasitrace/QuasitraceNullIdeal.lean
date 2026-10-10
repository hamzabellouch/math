import OAI.Analysis.Pureness.Quasitrace.QuasitraceCauchyAlgebra
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.Congruence.Basic

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open CuntzTrace Filter
open scoped Topology NNReal ENNReal
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (hadd : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)

instance cauchySequenceCompleteSpace : CompleteSpace (T.cauchySequenceAlgebra hadd) :=
  (T.cauchySequenceAlgebra_isClosed hadd).completeSpace_coe
instance cauchySequenceCStarAlgebra : CStarAlgebra (T.cauchySequenceAlgebra hadd) where

def nullSequenceIdeal : TwoSidedIdeal (T.cauchySequenceAlgebra hadd) :=
  TwoSidedIdeal.mk' {u | T.IsMetricNull (fun k => u.1 k)}
    T.isMetricNull_zero
    (fun hu hv => T.isMetricNull_add hadd hu hv)
    (fun hu => T.isMetricNull_neg hu)
    (fun {sequence _} hnull => T.isMetricNull_mul_left hnull ‖sequence.1‖ (norm_nonneg _)
      (lp.norm_apply_le_norm ENNReal.top_ne_zero sequence.1))
    (fun {_ sequence} hnull => T.isMetricNull_mul_right hnull ‖sequence.1‖ (norm_nonneg _)
      (lp.norm_apply_le_norm ENNReal.top_ne_zero sequence.1))

lemma nullSequenceIdeal_mem (u : T.cauchySequenceAlgebra hadd) :
    u ∈ T.nullSequenceIdeal hadd ↔ T.IsMetricNull (fun k => u.1 k) :=
  TwoSidedIdeal.mem_mk' (R := T.cauchySequenceAlgebra hadd) _ _ _ _ _ _ u

lemma nullSequenceIdeal_star {u : T.cauchySequenceAlgebra hadd}
    (hu : u ∈ T.nullSequenceIdeal hadd) : star u ∈ T.nullSequenceIdeal hadd :=
  by
    rw [nullSequenceIdeal_mem] at hu ⊢
    exact T.isMetricNull_star hu

include hadd
lemma metricNull_isClosed : IsClosed {u : lp (fun _ : ℕ => D) ∞ | T.IsMetricNull (fun k => u k)} := by
  apply isClosed_of_closure_subset
  intro u hu
  change T.IsMetricNull (fun k => u k)
  rw [IsMetricNull,Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ,hδ,hδsize⟩ := T.exists_norm_delta (ε/2) (by linarith)
  obtain ⟨v,hv,huv⟩ := Metric.mem_closure_iff.mp hu δ hδ
  have hnear (k : ℕ) : T.metricSize (u k-v k) < ε/2 := by
    apply hδsize
    exact (lp.norm_apply_le_norm ENNReal.top_ne_zero (u-v) k).trans_lt
      (by simpa only [dist_eq_norm] using huv)
  have he := (Metric.tendsto_nhds.mp hv) (ε/2) (by linarith)
  filter_upwards [he] with k hk
  have hk' : T.metricSize (v k) < ε/2 := by
    simpa only [Real.dist_eq,sub_zero,abs_of_nonneg (T.metricSize_nonneg _)] using hk
  have ht := hadd (u k-v k) (v k)
  rw [sub_add_cancel] at ht
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (T.metricSize_nonneg _)]
  linarith [hnear k]

lemma nullSequenceIdeal_isClosed : IsClosed (T.nullSequenceIdeal hadd : Set (T.cauchySequenceAlgebra hadd)) :=
  by
    have he : (T.nullSequenceIdeal hadd : Set (T.cauchySequenceAlgebra hadd)) =
        {u | T.IsMetricNull (fun k => u.1 k)} := Set.ext (T.nullSequenceIdeal_mem hadd)
    rw [he]
    exact (T.metricNull_isClosed hadd).preimage continuous_subtype_val

abbrev CauchyQuotient := (T.nullSequenceIdeal hadd).ringCon.Quotient

def cauchyQuotientMap : T.cauchySequenceAlgebra hadd →ₐ[ℂ] T.CauchyQuotient hadd :=
  (T.nullSequenceIdeal hadd).ringCon.mkₐ ℂ

lemma cauchyQuotientMap_surjective : Function.Surjective (T.cauchyQuotientMap hadd) :=
  (T.nullSequenceIdeal hadd).ringCon.mkₐ_surjective (α := ℂ)
end CuntzPureness.PositiveQuasitrace

end

end OAI
