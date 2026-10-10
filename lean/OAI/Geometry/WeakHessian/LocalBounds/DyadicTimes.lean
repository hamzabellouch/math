import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.HalfTime

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped Topology ENNReal NNReal
open Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
open Set Filter Topology Bornology
open scoped InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace WeakHessian
lemma continuous_halfTime : Continuous halfTime :=
  (continuous_subtype_val.div_const _).subtype_mk _
lemma continuous_rightTime : Continuous rightTime :=
  ((continuous_subtype_val.add_const _).div_const _).subtype_mk _

lemma dist_halfTime (s t : Time) : dist (halfTime s) (halfTime t) = dist s t / 2 := by
  change |(s:ℝ)/2-(t:ℝ)/2| = |(s:ℝ)-(t:ℝ)|/2
  rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
lemma dist_rightTime (s t : Time) : dist (rightTime s) (rightTime t) = dist s t / 2 := by
  change |((s:ℝ)+1)/2-((t:ℝ)+1)/2| = |(s:ℝ)-(t:ℝ)|/2
  rw [← sub_div, add_sub_add_right_eq_sub, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]

@[simp] lemma halfTime_zero : halfTime timeZero = timeZero := by
  apply Subtype.ext; norm_num [halfTime,timeZero]
@[simp] lemma rightTime_one : rightTime timeOne = timeOne := by
  apply Subtype.ext; norm_num [rightTime,timeOne]
lemma halfTime_one_eq_rightTime_zero : halfTime timeOne = rightTime timeZero := by
  apply Subtype.ext; norm_num [halfTime,rightTime,timeOne,timeZero]

def dyadicTimes : ℕ → Set Time
  | 0 => {timeZero,timeOne}
  | n+1 => halfTime '' dyadicTimes n ∪ rightTime '' dyadicTimes n

lemma zero_mem_dyadicTimes (n : ℕ) : timeZero ∈ dyadicTimes n := by
  induction n with
  | zero => simp [dyadicTimes]
  | succ n hn => exact Or.inl ⟨timeZero,hn,halfTime_zero⟩
lemma one_mem_dyadicTimes (n : ℕ) : timeOne ∈ dyadicTimes n := by
  induction n with
  | zero => simp [dyadicTimes]
  | succ n hn => exact Or.inr ⟨timeOne,hn,rightTime_one⟩

lemma monotone_dyadicTimes : Monotone dyadicTimes := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero =>
    intro t ht
    rcases ht with rfl | ht
    · exact zero_mem_dyadicTimes 1
    · have he : t = timeOne := ht
      rw [he]
      exact one_mem_dyadicTimes 1
  | succ n hn =>
    exact union_subset_union (image_mono hn) (image_mono hn)

lemma exists_dyadicTime_dist_le (n : ℕ) (t : Time) :
    ∃ s ∈ dyadicTimes n, dist s t ≤ (1/2:ℝ)^n := by
  induction n generalizing t with
  | zero =>
    refine ⟨timeZero,zero_mem_dyadicTimes 0,?_⟩
    change |0-(t:ℝ)| ≤ (1/2:ℝ)^0
    simpa only [zero_sub, abs_neg, abs_of_nonneg t.2.1, pow_zero] using t.2.2
  | succ n hn =>
    by_cases ht : (t:ℝ) ≤ 1/2
    · let u : Time := ⟨2*(t:ℝ), by constructor <;> linarith [t.2.1]⟩
      have hu : halfTime u = t := by apply Subtype.ext; dsimp [halfTime,u]; ring
      obtain ⟨s,hs,hsd⟩ := hn u
      refine ⟨halfTime s,Or.inl ⟨s,hs,rfl⟩,?_⟩
      rw [← hu,dist_halfTime,pow_succ]
      linarith
    · let u : Time := ⟨2*(t:ℝ)-1, by constructor <;> linarith [t.2.2]⟩
      have hu : rightTime u = t := by apply Subtype.ext; dsimp [rightTime,u]; ring
      obtain ⟨s,hs,hsd⟩ := hn u
      refine ⟨rightTime s,Or.inr ⟨s,hs,rfl⟩,?_⟩
      rw [← hu,dist_rightTime,pow_succ]
      linarith

lemma dense_dyadicTimes : Dense (⋃ n, dyadicTimes n) := by
  intro t
  rw [Metric.mem_closure_iff]
  intro ε hε
  have ht : Tendsto (fun n : ℕ => (1/2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨n,hn⟩ := ((tendsto_order.mp ht).2 ε hε).exists
  obtain ⟨s,hs,hsd⟩ := exists_dyadicTime_dist_le n t
  exact ⟨s,mem_iUnion.mpr ⟨n,hs⟩,by simpa only [dist_comm] using hsd.trans_lt hn⟩

end WeakHessian

end
end InlinedFile0

end OAI
