import Mathlib
import OAI.Combinatorics.KMedian.Expanders.WalkMoments
import OAI.Combinatorics.KMedian.Expanders.WalkSegments

namespace OAI

section Inline_PCPPathCount

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace PortGraph
variable {V D : Type}
variable (G : PortGraph V D) (bad : V × D → Prop)

lemma badCount_eq_sum (n : ℕ) (v : V) (c : Fin n → D) :
    G.badCount bad n v c = ∑ i : Fin n, G.edgeHit bad (G.trace n v c i.castSucc) (c i) := by
  induction n generalizing v with
  | zero => simp [badCount]
  | succ n ih =>
    rw [badCount,Fin.sum_univ_succ]
    simp only [trace_zero, Fin.castSucc_zero, Fin.castSucc_succ, trace_succ]
    rw [ih]

namespace Walk
variable {G bad} {n : ℕ}
noncomputable def ithHit (p : G.Walk n) (i : ℕ) : ℝ :=
  if h : i < n then G.edgeHit bad (p.vertex ⟨i,by omega⟩) (p.port ⟨i,h⟩) else 0
noncomputable def hitCount (p : G.Walk n) : ℝ := ∑ i ∈ range n, p.ithHit (bad := bad) i

lemma ithHit_nonneg (p : G.Walk n) (i : ℕ) : 0 ≤ p.ithHit (bad := bad) i := by
  unfold ithHit
  split_ifs
  · exact (G.edgeHit_bounds bad _ _).1
  · rfl

lemma hitCount_eq (p : G.Walk n) :
    p.hitCount (bad := bad) = G.badCount bad n (p.vertex 0) p.port := by
  rw [G.badCount_eq_sum bad]
  unfold hitCount
  rw [← Fin.sum_univ_eq_sum_range (fun i => p.ithHit (bad := bad) i)]
  apply sum_congr rfl
  intro i _
  simp only [ithHit,dite_eq_left i.isLt]
  have hp := congrFun p.vertex_eq_trace i.castSucc
  rw [← hp]
  rfl

lemma hitCount_nonneg (p : G.Walk n) : 0 ≤ p.hitCount (bad := bad) :=
  sum_nonneg (fun i _ => p.ithHit_nonneg i)

lemma partial_hits_le (p : G.Walk n) (m : ℕ) :
    (∑ i ∈ range m, p.ithHit (bad := bad) i) ≤ p.hitCount (bad := bad) := by
  let N := max m n
  have hs : ∑ i ∈ range N, p.ithHit (bad := bad) i = p.hitCount (bad := bad) := by
    unfold hitCount
    symm
    apply sum_subset (range_mono (le_max_right m n))
    intro i _ hi
    have hh : ¬ i < n := by simpa only [mem_range] using hi
    simp [ithHit,hh]
  rw [← hs]
  exact sum_le_sum_of_subset_of_nonneg (range_mono (le_max_left m n))
    (fun i _ _ => p.ithHit_nonneg i)

lemma prefix_hitCount_le (p : G.Walk n) (m : ℕ) (hm : m ≤ n) :
    (p.segment 0 m (by omega)).hitCount (bad := bad) ≤ p.hitCount (bad := bad) := by
  have hs : (p.segment 0 m (by omega)).hitCount (bad := bad) =
      ∑ i ∈ range m, p.ithHit (bad := bad) i := by
    unfold hitCount
    apply sum_congr rfl
    intro i hi
    have him : i < m := mem_range.mp hi
    have hin : i < n := by omega
    simp [ithHit,him,hin,segment]
  rw [hs]
  exact p.partial_hits_le m

variable [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]

lemma hitCount_second_moment (hsym : ∀ z, bad (G.rotate z) ↔ bad z)
    (hG : G.Contracts (1/2)) :
    (𝔼 p : G.Walk n, (p.hitCount (bad := bad))^2) ≤
      5*n*testRate bad + (n:ℝ)^2*(testRate bad)^2 := by
  simp_rw [hitCount_eq]
  have he := Fintype.expect_equiv (wordEquiv (G := G) (n := n))
    (fun p : G.Walk n => (G.badCount bad n (p.vertex 0) p.port)^2)
    (fun z : V × (Fin n → D) => (G.badCount bad n z.1 z.2)^2) (fun _ => rfl)
  rw [he,expect_prod]
  exact G.countSquareMean_le bad hsym hG n

end Walk
end PortGraph
end MetricKMedian.PCP

end Inline_PCPPathCount

end OAI
