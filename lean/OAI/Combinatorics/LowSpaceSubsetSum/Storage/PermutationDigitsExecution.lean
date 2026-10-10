import OAI.Combinatorics.LowSpaceSubsetSum.Storage.PermutationArray

namespace OAI

/-! # Reading bounded permutation choices into stored digits

The recursive execution stops after a failed range draw and never evaluates
the ideal backup permutation. Accepted digits materialize the exact bounded
sampler output by the integer-digit array construction.
-/

noncomputable section

namespace LowSpaceSubsetSum.PermutationDigitsExecution

open PermutationArray

def run (n : ℕ) : (k : ℕ) → (permutationCoupling n k).Seed →
    SamplerExecution.Trace (Digits k)
  | 0, _ => ⟨some (), 0, 0⟩
  | k + 1, s =>
    let first := (SamplerExecution.fin n (k + 1)).run s.1
    match first.value with
    | none => ⟨none, first.reads, first.tests⟩
    | some p =>
      let rest := run n k s.2
      ⟨rest.value.map (fun r => (p, r)), first.reads + rest.reads, first.tests + rest.tests⟩

theorem value (n k : ℕ) (s : (permutationCoupling n k).Seed) :
    ((run n k s).value.map (semantic k)) = ((SamplerExecution.permutation n k).run s).value := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rcases s with ⟨head, tail⟩
    have hi := ih tail
    generalize hf : (SamplerExecution.fin n (k + 1)).run head = first
    cases hv : first.value with
    | none =>
      simp only [run, hf, hv, Option.map_none]
      simp only [SamplerExecution.permutation, SamplerExecution.map, SamplerExecution.prod,
        SamplerExecution.bind, hf, hv, ↓reduceIte, Option.map_none]
    | some p =>
      have hp := (SamplerExecution.fin n (k + 1)).ideal_eq_of_some head p (by rw [hf, hv])
      simp only [run, hf, hv, SamplerExecution.permutation, SamplerExecution.map,
        SamplerExecution.prod, SamplerExecution.bind, reduceCtorEq, ↓reduceIte, Option.map_map]
      rw [← hi]
      simp only [Option.map_map, semantic, hp]
      rfl

theorem counts (n k : ℕ) (s : (permutationCoupling n k).Seed) :
    (run n k s).reads ≤ k * n ^ 3 ∧ (run n k s).tests = 0 := by
  induction k with
  | zero => simp [run]
  | succ k ih =>
    have hf := SamplerExecution.fin_bounded n (k + 1) s.1
    have hr := ih s.2
    simp only [run]
    split
    · dsimp only
      constructor
      · exact hf.1.trans (by nlinarith)
      · omega
    · dsimp only
      constructor
      · nlinarith only [hf.1, hr.1]
      · omega

def materialize (n k : ℕ) (s : (permutationCoupling n k).Seed) :
    Option (Vector (Fin k) k) × ℕ :=
  let digits := run n k s
  match digits.value with
  | none => (none, 1)
  | some d =>
    let out := build k d
    (some out.1, out.2 + 1)

theorem materialize_work (n k : ℕ) (s : (permutationCoupling n k).Seed) :
    (materialize n k s).2 ≤ 10 * (k + 1) ^ 2 + 1 := by
  simp only [materialize]
  split
  · dsimp only; omega
  · exact Nat.add_le_add_right (build_work k _) 1

theorem materialize_value (n k : ℕ) (s : (permutationCoupling n k).Seed)
    (v : Vector (Fin k) k) (h : (materialize n k s).1 = some v) :
    ∃ e, ((SamplerExecution.permutation n k).run s).value = some e ∧
      ∀ i : Fin k, v[i.val] = e i := by
  simp only [materialize] at h
  split at h
  · contradiction
  next d hd =>
    cases h
    refine ⟨semantic k d, ?_, build_value k d⟩
    rw [← value, hd]
    rfl

end LowSpaceSubsetSum.PermutationDigitsExecution

end

end OAI
