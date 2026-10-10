import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionArrayBuild

namespace OAI

/-! # Live cells for the two materialized compression pair lists

The recursive tail, current mapped row, append frames and output list are
all included. Repeated weights remain distinct occurrences.
-/

namespace LowSpaceSubsetSum.CompressionPairCells

def run : List ℤ → List ℤ → (List ℤ × ℕ) × ℕ
  | [], ys => (([], 1), 4*(ys.length+1))
  | x :: xs, ys =>
    let rest := run xs ys
    let row := ys.map (x+·)
    let out := row++rest.1.1
    ((out, rest.1.2+3*ys.length+2),
      max (rest.2+8) (4*(out.length+ys.length+1)+8))

theorem value (xs ys : List ℤ) : (run xs ys).1 = CompressionArrayBuild.pairSums xs ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [run, CompressionArrayBuild.pairSums, ih]

theorem length (xs ys : List ℤ) : (run xs ys).1.1.length = xs.length*ys.length := by
  rw [value, CompressionArrayBuild.pairSums_value, pairSumList_length]

theorem cells (xs ys : List ℤ) :
    (run xs ys).2 ≤ 16*(xs.length*ys.length+xs.length+ys.length+1) := by
  induction xs with
  | nil => simp only [run, List.length_nil, Nat.zero_mul, Nat.zero_add]; omega
  | cons x xs ih =>
    simp only [run, List.length_cons, List.length_append, List.length_map, length]
    apply max_le
    · nlinarith only [ih]
    · nlinarith only [Nat.zero_le (xs.length*ys.length)]

end LowSpaceSubsetSum.CompressionPairCells

end OAI
