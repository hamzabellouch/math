import Mathlib
import OAI.Combinatorics.KMedian.Instance
import OAI.Combinatorics.KMedian.Sparse.SparseDeletion
import OAI.Combinatorics.KMedian.Reduction.RadiusPacking

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

variable {I : Instance}
local instance sparsificationPseudoMetricSpace : PseudoMetricSpace (Fin I.n) := I.pseudoMetric

theorem nearest_triangle {O : Finset (Fin I.n)} (hO : O.Nonempty) (i j : Fin I.n) :
    nearest I i O ≤ dist i j+nearest I j O := by
  obtain ⟨o,ho,he⟩ := I.nearest_attained j O hO
  rw [he]
  exact (I.nearest_le i ho).trans (dist_triangle i j o)

theorem denseBall_cost {O : Finset (Fin I.n)} (hO : O.Nonempty) (i : Fin I.n) :
    nearest I i O*(denseBall (I:=I) O i).card ≤
      (3/2:ℝ)*∑ j ∈ denseBall (I:=I) O i, nearest I j O := by
  have hp : ∀ j ∈ denseBall (I:=I) O i, nearest I i O ≤ (3/2:ℝ)*nearest I j O := by
    intro j hj
    have hnear := (mem_filter.mp hj).2
    have hh := nearest_triangle hO i j
    rw [dist_comm i j] at hh
    linarith only [hnear,hh]
  have hs := sum_le_sum hp
  simp only [sum_const,nsmul_eq_mul,← mul_sum] at hs
  simpa only [mul_comm (nearest I i O)] using hs

theorem denseBall_disjoint {O : Finset (Fin I.n)} {i p : Fin I.n}
    (hi : nearest I i O ≤ dist i p) (hp : nearest I p O ≤ dist i p) :
    Disjoint (denseBall (I:=I) O i) (denseBall (I:=I) O p) := by
  apply disjoint_left.mpr
  intro j hj1 hj2
  have h1 := (mem_filter.mp hj1).2
  have h2 := (mem_filter.mp hj2).2
  have ht := dist_triangle i j p
  rw [dist_comm i j] at ht
  have hn := dist_nonneg (x:=i) (y:=p)
  linarith only [hi,hp,h1,h2,ht,hn]

theorem sparsify (F O : Finset (Fin I.n)) (hOF : O ⊆ F) (hO : O.Nonempty)
    (hcost : 0 < cost I O) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ P : Finset (Fin I.n), P ⊆ F ∧ (P.card:ℝ)*ρ ≤ 3/2 ∧
      let F' := F.filter (fun i => ∀ p ∈ P, nearest I p O ≤ dist p i)
      O ⊆ F' ∧ Sparse (I:=I) F' O ρ := by
  classical
  let D := F.filter (fun i => ρ*cost I O < nearest I i O*(denseBall (I:=I) O i).card)
  have hpos : ∀ i ∈ D, 0 < nearest I i O := by
    intro i hi
    have hd := (mem_filter.mp hi).2
    have hh : 0 < nearest I i O*(denseBall (I:=I) O i).card := (mul_pos hρ hcost).trans hd
    exact (mul_pos_iff.mp hh).elim (fun h => h.1) (fun h => (h.2.not_ge (Nat.cast_nonneg _)).elim)
  obtain ⟨P,hPD,hsep,hcover⟩ := radius_packing D (fun i => nearest I i O) hpos
  have hPF : P ⊆ F := hPD.trans (filter_subset _ _)
  have hdisj : Set.PairwiseDisjoint (↑P) (denseBall (I:=I) O) := by
    intro i hi p hp hip
    have h1 := hsep i hi p hp hip
    have h2 := hsep p hp i hi (Ne.symm hip)
    rw [dist_comm p i] at h2
    exact denseBall_disjoint h1 h2
  have hpoint : ∀ p ∈ P, ρ*cost I O ≤ (3/2:ℝ)*∑ j ∈ denseBall (I:=I) O p, nearest I j O := by
    intro p hp
    exact (mem_filter.mp (hPD hp)).2.le.trans (denseBall_cost hO p)
  have hsum := sum_le_sum hpoint
  simp only [sum_const,nsmul_eq_mul,← mul_sum,← sum_biUnion hdisj] at hsum
  have hJ : P.biUnion (denseBall (I:=I) O) ⊆ I.clients := by
    intro j hj
    obtain ⟨p,_,hp⟩ := mem_biUnion.mp hj
    exact (mem_filter.mp hp).1
  have hcostUnion : (∑ j ∈ P.biUnion (denseBall (I:=I) O), nearest I j O) ≤ cost I O :=
    sum_le_sum_of_subset_of_nonneg hJ (fun j _ _ => I.nearest_nonneg j O)
  have hcount : (P.card:ℝ)*ρ ≤ 3/2 := by
    apply (mul_le_mul_iff_left₀ hcost).mp
    have hh := hsum.trans (mul_le_mul_of_nonneg_left hcostUnion (by norm_num : (0:ℝ) ≤ 3/2))
    nlinarith only [hh]
  refine ⟨P,hPF,hcount,?_,?_⟩
  · intro o ho
    exact mem_filter.mpr ⟨hOF ho,fun p _ => I.nearest_le p ho⟩
  · intro i hi
    by_contra hn
    have hiD : i ∈ D := mem_filter.mpr ⟨(mem_filter.mp hi).1,lt_of_not_ge hn⟩
    obtain ⟨p,hp,hclose,_⟩ := hcover i hiD
    have hfar := (mem_filter.mp hi).2 p hp
    rw [dist_comm i p] at hclose
    exact hclose.not_ge hfar

end MetricKMedian.Reduction
end
end

end OAI
