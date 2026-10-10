import Mathlib
import OAI.Geometry.CAT0Fillings.Swept.Current
import OAI.Geometry.CAT0Fillings.Calculus.Piecewise
import OAI.Geometry.CAT0Fillings.Calculus.ClosedLevel

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ClosedCalculus
lemma min_const_deriv_low {N t : ℝ} (ht : t < N) :
    HasDerivAt (fun z => min z N) 1 t := by
  apply (hasDerivAt_id t).congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds ht] with z hz
  exact min_eq_left hz.le
lemma min_const_deriv_high {N t : ℝ} (ht : N < t) :
    HasDerivAt (fun z => min z N) 0 t := by
  apply (hasDerivAt_const t N).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with z hz
  exact min_eq_right hz.le
lemma min_const_lipschitz (N : ℝ) : LipschitzWith 1 (fun z : ℝ => min z N) := by
  simpa using (LipschitzWith.id.min (LipschitzWith.const N))
end CAT0Fillings.ClosedCalculus
namespace CAT0Fillings.ChartGeometry
open ClosedCalculus

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)
lemma closed_min_const (hz : IsCycle T) (P : q.Sobolev) (N : ℝ) :
    ∃ Q : q.Sobolev,
      (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => min (q.inclusion P x) N) ∧
      (q.closedGradient Q : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => if q.inclusion P (q.atlasParam w) < N then q.closedGradient P w else 0) := by
  have hd (t : ℝ) (ht : t ∉ ({N} : Set ℝ)) : DifferentiableAt ℝ (fun z => min z N) t := by
    rcases lt_or_gt_of_ne (show t ≠ N from ht) with h | h
    · exact (min_const_deriv_low h).differentiableAt
    · exact (min_const_deriv_high h).differentiableAt
  obtain ⟨Q,hQ,hG⟩ := q.closed_chain_countable (min_const_lipschitz N) (countable_singleton N) hd hz P
  refine ⟨Q,hQ,?_⟩
  filter_upwards [hG,q.closedGradient_level_zero hz P N] with w hw hzN
  rw [hw]
  by_cases h : q.inclusion P (q.atlasParam w) < N
  · rw [ite_eq_left h,(min_const_deriv_low h).deriv,one_smul]
  · rw [ite_eq_right h]
    rcases (le_of_not_gt h).eq_or_lt with he | he
    · rw [hzN he.symm,smul_zero]
    · rw [(min_const_deriv_high he).deriv,zero_smul]
end CAT0Fillings.ChartGeometry
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ClosedCalculus
lemma max_const_deriv_low {N t : ℝ} (ht : t < N) :
    HasDerivAt (fun z => max z N) 0 t := by
  apply (hasDerivAt_const t N).congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds ht] with z hz
  exact max_eq_right hz.le
lemma max_const_deriv_high {N t : ℝ} (ht : N < t) :
    HasDerivAt (fun z => max z N) 1 t := by
  apply (hasDerivAt_id t).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with z hz
  exact max_eq_left hz.le
lemma max_const_lipschitz (N : ℝ) : LipschitzWith 1 (fun z : ℝ => max z N) := by
  simpa using (LipschitzWith.id.max (LipschitzWith.const N))
end CAT0Fillings.ClosedCalculus
namespace CAT0Fillings.ChartGeometry
open ClosedCalculus

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)
lemma closed_max_const (hz : IsCycle T) (P : q.Sobolev) (N : ℝ) :
    ∃ Q : q.Sobolev,
      (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => max (q.inclusion P x) N) ∧
      (q.closedGradient Q : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => if N < q.inclusion P (q.atlasParam w) then q.closedGradient P w else 0) := by
  have hd (t : ℝ) (ht : t ∉ ({N} : Set ℝ)) : DifferentiableAt ℝ (fun z => max z N) t := by
    rcases lt_or_gt_of_ne (show t ≠ N from ht) with h | h
    · exact (max_const_deriv_low h).differentiableAt
    · exact (max_const_deriv_high h).differentiableAt
  obtain ⟨Q,hQ,hG⟩ := q.closed_chain_countable (max_const_lipschitz N) (countable_singleton N) hd hz P
  refine ⟨Q,hQ,?_⟩
  filter_upwards [hG,q.closedGradient_level_zero hz P N] with w hw hzN
  rw [hw]
  by_cases h : N < q.inclusion P (q.atlasParam w)
  · rw [ite_eq_left h,(max_const_deriv_high h).deriv,one_smul]
  · rw [ite_eq_right h]
    rcases (le_of_not_gt h).eq_or_lt with he | he
    · rw [hzN he,smul_zero]
    · rw [(max_const_deriv_low he).deriv,zero_smul]
end CAT0Fillings.ChartGeometry
end

end OAI
