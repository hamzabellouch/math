import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionWeights
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.PreparedCompressionPass

namespace OAI

/-! # Building the compression trial's stored arrays

All seven compact lists are materialized once. Their capacity test precedes
raw-list and pair-list construction. The resulting arrays are shared by all
residue passes.
-/

namespace LowSpaceSubsetSum.CompressionArrayBuild

open scoped BigOperators
variable {n : ℕ}

def pairSums : List ℤ → List ℤ → List ℤ × ℕ
  | [], _ => ([], 1)
  | x :: xs, ys =>
    let rest := pairSums xs ys
    ((ys.map (x + ·)) ++ rest.1, rest.2 + 3 * ys.length + 2)

theorem pairSums_value (xs ys : List ℤ) : (pairSums xs ys).1 = pairSumList xs ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [pairSums, ih, pairSumList, List.product]

theorem pairSums_work (xs ys : List ℤ) :
    (pairSums xs ys).2 = (3 * ys.length + 2) * xs.length + 1 := by
  induction xs with
  | nil => simp [pairSums]
  | cons x xs ih => simp only [pairSums, ih, List.length_cons, Nat.mul_add, Nat.mul_one]; omega

theorem pairSums_work_le (xs ys : List ℤ) (hy : 0 < ys.length) :
    (pairSums xs ys).2 ≤ 5 * (pairSumList xs ys).length + 1 := by
  rw [pairSums_work, pairSumList_length]
  nlinarith only [Nat.le_mul_of_pos_right xs.length hy]

structure Blocks (n : ℕ) where
  compact : Fin 7 → List (Fin n)
  left : List (Fin n)
  right : Fin 2 → List (Fin n)

def compactLists (a : Fin n → ℤ) (V : Blocks n) : Vector (List ℤ × ℕ) 7 :=
  Vector.ofFn (fun i => CompressionWeights.compact a (V.compact i))

def passed (lists : Vector (List ℤ × ℕ) 7) (cap : ℕ) : Bool :=
  decide (∀ i : Fin 7, (lists[i.val].1).length ≤ cap)

def assemble (lists : Vector (List ℤ × ℕ) 7) (l r₀ r₁ : List ℤ) :
    PreparedCompressionPass.Arrays × ℕ :=
  let p₀ := pairSums lists[1].1 r₀
  let p₁ := pairSums lists[3].1 r₁
  let A : PreparedCompressionPass.Arrays :=
    ⟨![lists[4].1.toArray, lists[6].1.toArray, lists[0].1.toArray, lists[2].1.toArray],
      ![lists[5].1.toArray, l.toArray, p₀.1.toArray, p₁.1.toArray]⟩
  (A, p₀.2 + p₁.2 + PreparedCompressionPass.size A + 10)

def run (a : Fin n → ℤ) (V : Blocks n) (cap : ℕ) :
    Option PreparedCompressionPass.Arrays × ℕ :=
  let lists := compactLists a V
  let cw := ∑ i : Fin 7, (lists[i.val].2 + lists[i.val].1.length)
  if passed lists cap then
    let l := CompressionWeights.raw a V.left
    let r₀ := CompressionWeights.raw a (V.right 0)
    let r₁ := CompressionWeights.raw a (V.right 1)
    let out := assemble lists l.1 r₀.1 r₁.1
    (some out.1, cw + l.2 + r₀.2 + r₁.2 + out.2 + 30)
  else (none, cw + 30)

def source (D : CompressionData n) (e : Equiv.Perm (Fin n)) : Blocks n :=
  ⟨fun i => (D.block e i).sort (· ≤ ·), (D.leftRaw e).sort (· ≤ ·),
    fun i => (D.rightRaw e i).sort (· ≤ ·)⟩

theorem compactLists_source (D : CompressionData n) (e : Equiv.Perm (Fin n)) (i : Fin 7) :
    ((compactLists D.weights (source D e))[i.val]).1 = compactWeightList D.weights (D.block e i) := by
  simp only [compactLists, Vector.getElem_ofFn, source, CompressionWeights.compact_source]

theorem passed_source (D : CompressionData n) (e : Equiv.Perm (Fin n)) :
    passed (compactLists D.weights (source D e)) (2 ^ CompressionSetup.executableCapExponent n) =
      D.compactTests e := by
  simp only [passed, compactLists_source, CompressionData.compactTests]

theorem assemble_source (D : CompressionData n) (e : Equiv.Perm (Fin n)) :
    (assemble (compactLists D.weights (source D e))
      (CompressionWeights.raw D.weights (source D e).left).1
      (CompressionWeights.raw D.weights ((source D e).right 0)).1
      (CompressionWeights.raw D.weights ((source D e).right 1)).1).1 =
        PreparedCompressionPass.source D e := by
  simp only [assemble, compactLists, Vector.getElem_ofFn, source,
    CompressionWeights.compact_source, CompressionWeights.raw_source, pairSums_value,
    PreparedCompressionPass.source, CompressionData.storedFirst, CompressionData.storedSecond]
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem run_source (D : CompressionData n) (e : Equiv.Perm (Fin n)) :
    (run D.weights (source D e) (2 ^ CompressionSetup.executableCapExponent n)).1 =
      if D.compactTests e then some (PreparedCompressionPass.source D e) else none := by
  simp only [run, passed_source]
  split <;> simp only [assemble_source]

end LowSpaceSubsetSum.CompressionArrayBuild

end OAI
