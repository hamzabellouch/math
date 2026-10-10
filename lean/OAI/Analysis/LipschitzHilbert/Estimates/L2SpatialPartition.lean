import OAI.Analysis.LipschitzHilbert.Packets.PacketConvolution
import OAI.Analysis.LipschitzHilbert.Estimates.L2Indicator
import OAI.Analysis.LipschitzHilbert.Trees.SourceL2Gram
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace OAI

/-! Squaring and summing local L2 estimates over a measurable partition,
with a finite overlap bound for the enlarged input sets. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem l2Indicator_norm_sq (S : Set (ℝ×ℝ)) (hS : MeasurableSet S) (f : Lp ℂ 2 planeMeasure) :
    ‖l2Indicator planeMeasure S hS f‖^2=∫ z in S, ‖f z‖^2 ∂planeMeasure := by
  change ‖((Lp.memLp f).indicator hS).toLp (S.indicator f)‖^2=_
  rw [memLp_toL2_norm_sq]
  have he : (fun z => ‖S.indicator f z‖^2)=S.indicator (fun z => ‖f z‖^2) := by
    funext z
    by_cases hz : z∈S <;> simp [Set.indicator,hz]
  rw [he,integral_indicator hS]

theorem l2Indicator_finite_overlap {ι : Type*} (J : Finset ι) (S : ι → Set (ℝ×ℝ))
    (hS : ∀ i, MeasurableSet (S i)) (D : ℝ)
    (hD : ∀ z, (∑ i∈J, (S i).indicator (fun _ => (1:ℝ)) z)≤D)
    (f : Lp ℂ 2 planeMeasure) :
    (∑ i∈J, ‖l2Indicator planeMeasure (S i) (hS i) f‖^2)≤D*‖f‖^2 := by
  have hfi := (Lp.memLp f).integrable_norm_pow (by decide : 2≠0)
  have he (i : ι) : (fun z => (S i).indicator (fun _ => (1:ℝ)) z*‖f z‖^2)=
      (S i).indicator (fun z => ‖f z‖^2) := by
    funext z
    by_cases hz : z∈S i <;> simp [Set.indicator,hz]
  calc
    _ = ∑ i∈J, ∫ z, (S i).indicator (fun _ => (1:ℝ)) z*‖f z‖^2 ∂planeMeasure := by
      apply Finset.sum_congr rfl
      intro i _
      rw [l2Indicator_norm_sq,he,integral_indicator (hS i)]
    _ = ∫ z, ∑ i∈J, (S i).indicator (fun _ => (1:ℝ)) z*‖f z‖^2 ∂planeMeasure := by
      symm
      apply integral_finsetSum
      intro i _
      rw [he]
      exact hfi.indicator (hS i)
    _ ≤ ∫ z, D*‖f z‖^2 ∂planeMeasure := by
      apply integral_mono
      · apply integrable_finsetSum
        intro i _
        rw [he]
        exact hfi.indicator (hS i)
      · exact hfi.const_mul D
      · intro z
        change (∑ i∈J, (S i).indicator (fun _ => (1:ℝ)) z*‖f z‖^2)≤D*‖f z‖^2
        rw [←Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (hD z) (sq_nonneg _)
    _ = _ := by
      rw [integral_const_mul,←memLp_toL2_norm_sq planeMeasure _ (Lp.memLp f),Lp.toLp_coeFn]

theorem l2Indicator_partition_bound {ι : Type*} [Countable ι]
    (Q S : ι → Set (ℝ×ℝ)) (hQ : ∀ i, MeasurableSet (Q i)) (hS : ∀ i, MeasurableSet (S i))
    (hdisjoint : Pairwise (fun i j => Disjoint (Q i) (Q j))) (hcover : ⋃ i, Q i=univ)
    (B D : ℝ) (hB : 0≤B) (f g : Lp ℂ 2 planeMeasure)
    (hlocal : ∀ i, ‖l2Indicator planeMeasure (Q i) (hQ i) g‖^2≤
      B*‖l2Indicator planeMeasure (S i) (hS i) f‖^2)
    (hover : ∀ J : Finset ι, ∀ z, (∑ i∈J, (S i).indicator (fun _ => (1:ℝ)) z)≤D) :
    ‖g‖^2≤B*D*‖f‖^2 := by
  have hg := (Lp.memLp g).integrable_norm_pow (by decide : 2≠0)
  have hpartition := integral_iUnion (μ:=planeMeasure) (f:=fun z => ‖g z‖^2)
    hQ hdisjoint (by simpa only [hcover,integrableOn_univ] using hg)
  rw [hcover,setIntegral_univ] at hpartition
  have henergy : ‖g‖^2=∫ z, ‖g z‖^2 ∂planeMeasure := by
    simpa only [Lp.toLp_coeFn] using memLp_toL2_norm_sq planeMeasure g (Lp.memLp g)
  rw [henergy,hpartition]
  apply Real.tsum_le_of_sum_le (fun i => integral_nonneg fun _ => sq_nonneg _)
  intro J
  calc
    _ = ∑ i∈J, ‖l2Indicator planeMeasure (Q i) (hQ i) g‖^2 := by
      exact Finset.sum_congr rfl (fun i _ => (l2Indicator_norm_sq (Q i) (hQ i) g).symm)
    _ ≤ ∑ i∈J, B*‖l2Indicator planeMeasure (S i) (hS i) f‖^2 := Finset.sum_le_sum fun i _ => hlocal i
    _ = B*(∑ i∈J, ‖l2Indicator planeMeasure (S i) (hS i) f‖^2) := (Finset.mul_sum _ _ _).symm
    _ ≤ B*(D*‖f‖^2) := mul_le_mul_of_nonneg_left (l2Indicator_finite_overlap J S hS D (hover J) f) hB
    _ = _ := by ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
