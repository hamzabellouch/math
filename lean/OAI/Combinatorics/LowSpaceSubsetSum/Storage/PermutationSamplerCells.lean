import OAI.Combinatorics.LowSpaceSubsetSum.Storage.SamplerFinCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.PermutationDigitsExecution
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.Magnitudes

namespace OAI

/-! # Stored bounded draws and permutation digits

Each finite-range call uses an explicit candidate array and releases it
before the recursive tail. The conservative sum below also covers every
retained digit, scalar counter, and recursive return frame. A failed head
also counts the supplied but unread tail of the finite random-word tuple.
-/

noncomputable section
namespace LowSpaceSubsetSum.PermutationSamplerCells

def run (n : ℕ) : (k : ℕ) → (permutationCoupling n k).Seed →
    SamplerExecution.Trace (PermutationArray.Digits k) × ℕ
  | 0, _ => (⟨some (), 0, 0⟩, 8)
  | k+1, s =>
    let first := SamplerFinCells.run n (k+1) s.1
    match first.1.value with
    | none => (⟨none, first.1.reads, first.1.tests⟩, first.2+k*(3*n^3+88)+8)
    | some p =>
      let tail := run n k s.2
      (⟨tail.1.value.map (fun d => (p, d)), first.1.reads+tail.1.reads,
        first.1.tests+tail.1.tests⟩, first.2+tail.2+8)

theorem run_value (n k : ℕ) (s : (permutationCoupling n k).Seed) :
    (run n k s).1 = PermutationDigitsExecution.run n k s := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [run, SamplerFinCells.run_value, PermutationDigitsExecution.run]
    split <;> simp_all only

theorem run_cells (n k : ℕ) (s : (permutationCoupling n k).Seed) :
    (run n k s).2 ≤ k*(3*n^3+88)+8 := by
  induction k with
  | zero => simp only [run, Nat.zero_mul, Nat.zero_add, le_refl]
  | succ k ih =>
    have hf := SamplerFinCells.run_cells n (k+1) s.1
    have ht := ih s.2
    simp only [run]
    split
    · dsimp only
      nlinarith only [hf, Nat.zero_le (k*(3*n^3+88))]
    · dsimp only
      nlinarith only [hf, ht]

def materialize (n k : ℕ) (s : (permutationCoupling n k).Seed) :
    (Option (Vector (Fin k) k) × ℕ) × ℕ :=
  let digits := run n k s
  match digits.1.value with
  | none => ((none, 1), digits.2+16)
  | some d =>
    let out := PermutationArray.build k d
    ((some out.1, out.2+1), digits.2+PermutationArray.peakCells k+2*k+16)

theorem materialize_value (n k : ℕ) (s : (permutationCoupling n k).Seed) :
    (materialize n k s).1 = PermutationDigitsExecution.materialize n k s := by
  simp only [materialize, run_value, PermutationDigitsExecution.materialize]
  split <;> simp_all only

theorem materialize_cells (n k : ℕ) (s : (permutationCoupling n k).Seed) :
    (materialize n k s).2 ≤ (k+1)*(3*n^3+128) := by
  have hd := run_cells n k s
  have hp := PermutationArray.peakCells_bound k
  simp only [materialize]
  split <;> dsimp only <;> nlinarith only [hd, hp, Nat.zero_le (n^3)]

theorem materialize_cells_scale {n : ℕ} (I : Instance n) (hn : 10000 ≤ n)
    (k : ℕ) (hk : k ≤ n) (s : (permutationCoupling n k).Seed) :
    (materialize n k s).2 ≤ inputScale I^5 := by
  have hu : n+1 ≤ inputScale I := by unfold inputScale; omega
  have hu0 : 10000 ≤ inputScale I := by omega
  have hu3 : inputScale I ≤ inputScale I^3 := by
    simpa only [pow_one] using pow_le_pow_right' (by omega : 1 ≤ inputScale I)
      (by decide : 1 ≤ 3)
  have hc := Nat.pow_le_pow_left (show n ≤ inputScale I by omega) 3
  have ht : 3*n^3+128 ≤ 4*inputScale I^3 := by nlinarith only [hc, hu0, hu3]
  have hm := Nat.mul_le_mul (show k+1 ≤ inputScale I by omega) ht
  have hm' : (k+1)*(3*n^3+128) ≤ 4*inputScale I^4 := by
    convert hm using 1; ring
  have hp : 4*inputScale I^4 ≤ inputScale I^5 := by
    calc
      _ ≤ inputScale I*inputScale I^4 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  exact (materialize_cells n k s).trans (hm'.trans hp)

end LowSpaceSubsetSum.PermutationSamplerCells

end

end OAI
