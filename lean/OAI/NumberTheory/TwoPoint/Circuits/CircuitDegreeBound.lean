import OAI.NumberTheory.TwoPoint.Circuits.CircuitRecursiveApproximation

namespace OAI

/-! At fixed depth, the sampled polynomial degree is a power of the
sampling count times the logarithm of the circuit size. -/

namespace TwoPointCorrelations.AC0Circuit

open Finset
open scoped Classical

theorem approximationDegree_le {n : ℕ} (s : ℕ) (hs : 1 ≤ s)
    (c : AC0Circuit n) (m : ℕ) (hm : c.size ≤ m) :
    c.approximationDegree s ≤ (s * (Nat.log 2 m + 3)) ^ c.depth := by
  induction c generalizing m with
  | literal i b => simp [approximationDegree, depth]
  | @andGate k children ih | @orGate k children ih =>
    have hm' : 1 + ∑ i, (children i).size ≤ m := hm
    have hsize (i : Fin k) : (children i).size ≤ m := by
      have hh := single_le_sum (fun j _ => Nat.zero_le (children j).size) (mem_univ i)
      omega
    have hcount : k ≤ ∑ i, (children i).size := by
      calc
        k = ∑ _i : Fin k, 1 := by simp
        _ ≤ _ := sum_le_sum (fun i _ => (children i).size_pos)
    have hk : k ≤ m := by omega
    let B := s * (Nat.log 2 m + 3)
    let D := univ.sup (fun i => (children i).depth)
    have hB : 0 < B := by dsimp [B]; positivity
    have hsup : (univ.sup fun i => (children i).approximationDegree s) ≤ B ^ D := by
      apply Finset.sup_le
      intro i _
      exact (ih i m (hsize i)).trans
        (Nat.pow_le_pow_right hB (le_sup (f := fun i => (children i).depth) (mem_univ i)))
    have hlog : s * (Nat.log 2 k + 3) ≤ B :=
      Nat.mul_le_mul_left s (Nat.add_le_add_right (Nat.log_mono_right hk) 3)
    change (univ.sup fun i => (children i).approximationDegree s) * s *
      (Nat.log 2 k + 3) ≤ B ^ (1 + D)
    calc
      _ ≤ B ^ D * s * (Nat.log 2 k + 3) := by gcongr
      _ = B ^ D * (s * (Nat.log 2 k + 3)) := by ring
      _ ≤ B ^ D * B := Nat.mul_le_mul_left _ hlog
      _ = B ^ (1 + D) := by rw [Nat.add_comm 1 D, pow_succ]

end TwoPointCorrelations.AC0Circuit

end OAI
