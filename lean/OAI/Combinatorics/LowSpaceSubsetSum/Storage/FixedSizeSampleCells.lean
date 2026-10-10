import OAI.Combinatorics.LowSpaceSubsetSum.Storage.PermutationSamplerCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.FixedSizeCodeExecution
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredQueryCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.MeasuredFilterCells

namespace OAI

/-! # Live storage of one sampled separator mask

The accepted permutation is scanned into its first selected positions.
The resulting bounded list feeds the measured membership/code routines;
only the packed mask code survives this call.
-/

namespace LowSpaceSubsetSum.FixedSizeSampleCells

variable {g : ℕ}

def selected (v : Vector (Fin g) g) (k : ℕ) : List (Fin g) × ℕ :=
  let r := MeasuredFilterCells.run (fun i : Fin g => ((decide (i.val < k), 0), 4))
    (List.finRange g)
  (r.1.1.map (fun i => v[i.val]), r.2+3*g+8)

theorem prefix_value (v : Vector (Fin g) g) (k : ℕ) :
    (selected v k).1 = PermutationSubsetCode.prefixIndices v k := by
  simp only [selected, MeasuredFilterCells.run_value, MeasuredFilter.runAcc_value,
    List.reverse_nil, List.nil_append, PermutationSubsetCode.prefixIndices]

theorem prefix_length (v : Vector (Fin g) g) (k : ℕ) : (selected v k).1.length ≤ g := by
  rw [prefix_value]
  exact PermutationSubsetCode.prefix_length v k

theorem prefix_cells (v : Vector (Fin g) g) (k : ℕ) : (selected v k).2 ≤ 5*g+16 := by
  have h := MeasuredFilterCells.run_cells
    (fun i : Fin g => ((decide (i.val < k), 0), 4)) 4 (fun _ => le_rfl) (List.finRange g)
  simp only [List.length_finRange] at h
  change _+3*g+8 ≤ _
  omega

def pack (v : Vector (Fin g) g) (k : ℕ) : (Fin (2^g) × ℕ) × ℕ :=
  let xs := selected v k
  let out := StoredQueryCells.code g (fun i => StoredQueryCells.member i xs.1)
  ((⟨out.1.1, by
      rw [StoredQueryCells.code_value]
      simp only [StoredQueryCells.member_value]
      rw [StoredSeparatorQueries.code_value]
      exact (PaddedRows.index g (fun i => (CountedWeights.member i xs.1).1)).isLt⟩,
    out.1.2+4*g+3), xs.2+out.2+g+16)

theorem pack_value (v : Vector (Fin g) g) (k : ℕ) :
    (pack v k).1 = PermutationSubsetCode.pack v k := by
  have h := StoredQueryCells.code_value g (fun i => StoredQueryCells.member i (selected v k).1)
  simp only [StoredQueryCells.member_value, prefix_value] at h
  apply Prod.ext
  · apply Fin.ext
    change (StoredQueryCells.code g (fun i => StoredQueryCells.member i (selected v k).1)).1.1 = _
    simpa only [prefix_value, PermutationSubsetCode.pack] using congrArg Prod.fst h
  · change (StoredQueryCells.code g (fun i => StoredQueryCells.member i (selected v k).1)).1.2+
      4*g+3 = _
    simpa only [prefix_value, PermutationSubsetCode.pack] using congrArg (fun p : ℕ × ℕ => p.2+4*g+3) h

theorem pack_cells (v : Vector (Fin g) g) (k : ℕ) : (pack v k).2 ≤ 64*(g+1)^3 := by
  have hp := prefix_cells v k
  have hc := StoredQueryCells.code_cells g (4*(g+1))
    (fun i => StoredQueryCells.member i (selected v k).1) (fun i =>
      (StoredQueryCells.member_cells i _).trans
        (Nat.mul_le_mul_left 4 (Nat.add_le_add_right (prefix_length v k) 1)))
  change (selected v k).2+_+g+16 ≤ _
  nlinarith only [hp, hc, Nat.zero_le (g^2), Nat.zero_le (g^3)]

def reserve (n g : ℕ) : ℕ := (g+1)*(3*n^3+128)+128*(g+1)^3

noncomputable def run (n g k : ℕ) (s : (permutationCoupling n g).Seed) :
    (Option (Fin (2^g)) × ℕ) × ℕ :=
  let digits := PermutationSamplerCells.run n g s
  match digits.1.value with
  | none => ((none, digits.1.reads+1), digits.2+16)
  | some d =>
    let v := PermutationArray.build g d
    let out := pack v.1 k
    ((some out.1.1, digits.1.reads+v.2+out.1.2+2),
      digits.2+PermutationArray.peakCells g+out.2+2*g+24)

theorem run_value (n g k : ℕ) (s : (permutationCoupling n g).Seed) :
    (run n g k s).1 = FixedSizeCodeExecution.run n g k s := by
  simp only [run, PermutationSamplerCells.run_value, FixedSizeCodeExecution.run]
  split <;> simp_all only [pack_value]

theorem run_cells (n g k : ℕ) (s : (permutationCoupling n g).Seed) :
    (run n g k s).2 ≤ reserve n g := by
  have hd := PermutationSamplerCells.run_cells n g s
  have hp := PermutationArray.peakCells_bound g
  rw [run]
  split
  · dsimp only
    unfold reserve
    nlinarith only [hd, Nat.zero_le (n^3), Nat.zero_le (g^2), Nat.zero_le (g^3)]
  next d _ =>
    have hc := pack_cells (PermutationArray.build g d).1 k
    dsimp only
    unfold reserve
    nlinarith only [hd, hp, hc, Nat.zero_le (n^3), Nat.zero_le (g^2), Nat.zero_le (g^3)]

end LowSpaceSubsetSum.FixedSizeSampleCells

end OAI
