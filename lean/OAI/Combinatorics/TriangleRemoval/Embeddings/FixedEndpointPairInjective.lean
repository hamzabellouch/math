import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.RelativeSafeCopyIncrement

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma fixedEndpoint_pair_injective {n : ℕ} (u : Fin n) :
    Function.Injective (fun w : Fin n => ({u,w} : Finset (Fin n))) := by
  intro a b h
  change ({u,a} : Finset (Fin n)) = {u,b} at h
  have ha : a = u ∨ a = b := by
    have hh : a ∈ ({u,b} : Finset (Fin n)) := by rw [← h]; simp
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hh
  have hb : b = u ∨ b = a := by
    have hh : b ∈ ({u,a} : Finset (Fin n)) := by rw [h]; simp
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hh
  aesop

theorem wedge_copyEdgeLoad_le_two {n : ℕ} (u v : Fin n) (G : Graph n)
    (e : Finset (Fin n)) : copyEdgeLoad (wedgeEdges u v) G e ≤ 2 := by
  classical
  let A (x : Fin n) := Finset.univ.filter (fun w : Fin n => e = ({x,w} : Finset (Fin n)))
  have hA (x : Fin n) : (A x).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    apply fixedEndpoint_pair_injective x
    exact ((Finset.mem_filter.mp ha).2).symm.trans (Finset.mem_filter.mp hb).2
  have hf : Finset.univ.filter (fun w : Fin n => e ∈ wedgeEdges u v w) = A u ∪ A v := by
    ext w
    simp [A,wedgeEdges]
  have hc : (Finset.univ.filter (fun w : Fin n => e ∈ wedgeEdges u v w)).card ≤ 2 := by
    rw [hf]
    exact (Finset.card_union_le _ _).trans (by have := hA u; have := hA v; omega)
  unfold copyEdgeLoad
  calc
    _ ≤ ∑ w : Fin n, if e ∈ wedgeEdges u v w then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro w _
      by_cases h : e ∈ wedgeEdges u v w
      · rw [ite_eq_left h,ite_eq_left h]
        unfold intact
        split <;> norm_num
      · rw [ite_eq_right h,ite_eq_right h]
    _ = ((Finset.univ.filter (fun w : Fin n => e ∈ wedgeEdges u v w)).card : ℝ) := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ 2 := by exact_mod_cast hc

lemma wedge_copyLoadSafe {n : ℕ} (u v : Fin n) (G : Graph n) :
    copyLoadSafe (wedgeEdges u v) 2 G := by
  intro e _
  exact wedge_copyEdgeLoad_le_two u v G e

lemma wedge_pastRelativeCopyLoadsSafe {n : ℕ} (u v : Fin n) (T j : ℕ)
    (ω : History (Graph n) T) :
    pastRelativeCopyLoadsSafe (wedgeEdges u v) (fun _ => 2) T j ω := by
  intro k _
  exact wedge_copyLoadSafe u v _

end SharpTerminalLeave

end

end OAI
