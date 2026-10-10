import OAI.Combinatorics.LowSpaceSubsetSum.Compression.BudgetedCompressionSource

namespace OAI

/-! # Constructing the four live compression reader contexts

The eight input arrays are supplied once. Each right array is sorted and
retained by its returned context; row closures share that returned array.
-/

namespace LowSpaceSubsetSum.PreparedCompressionPass

open scoped BigOperators

structure Arrays where
  first : Fin 4 → Array ℤ
  second : Fin 4 → Array ℤ

def size (A : Arrays) : ℕ := (∑ i : Fin 4, ((A.first i).size + (A.second i).size)) + 1

def prepare (A : Arrays) (P t z : ℤ) (hP : 0 < P) :
    BudgetedCompressionPass.Data P t z × ℕ :=
  let a := CompressionContext.build (A.first 0) (A.second 0) P hP .direct
  let b := CompressionContext.build (A.first 1) (A.second 1) P hP (.complementary z)
  let c := CompressionContext.build (A.first 2) (A.second 2) P hP .direct
  let d := CompressionContext.build (A.first 3) (A.second 3) P hP (.complementary (t - z))
  (⟨a.1, b.1, c.1, d.1,
    (A.first 0).size * (A.second 0).size, (A.first 1).size * (A.second 1).size,
    (A.first 2).size * (A.second 2).size, (A.first 3).size * (A.second 3).size⟩,
    a.2 + b.2 + c.2 + d.2 + 16)

theorem prepare_work {n : ℕ} (I : Instance n) (hn : 10000 ≤ n)
    (A : Arrays) (P t z : ℤ) (hP : 0 < P)
    (hfirst : ∀ i, (A.first i).size ≤ 2 ^ n) (hsecond : ∀ i, (A.second i).size ≤ 2 ^ n) :
    (prepare A P t z hP).2 ≤ inputScale I ^ 6 * size A := by
  have h₀ := CompressionContext.build_work I hn (A.first 0) (A.second 0) P hP .direct
    (hfirst 0) (hsecond 0)
  have h₁ := CompressionContext.build_work I hn (A.first 1) (A.second 1) P hP (.complementary z)
    (hfirst 1) (hsecond 1)
  have h₂ := CompressionContext.build_work I hn (A.first 2) (A.second 2) P hP .direct
    (hfirst 2) (hsecond 2)
  have h₃ := CompressionContext.build_work I hn (A.first 3) (A.second 3) P hP (.complementary (t - z))
    (hfirst 3) (hsecond 3)
  have hu : 10000 ≤ inputScale I := by unfold inputScale; omega
  have h1 : 1 ≤ inputScale I ^ 5 := Nat.one_le_pow _ _ (by omega)
  have hm : 20 * inputScale I ^ 5 ≤ inputScale I ^ 6 := by
    calc
      _ ≤ inputScale I * inputScale I ^ 5 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  change _ + _ + _ + _ + 16 ≤ _
  unfold size
  rw [Fin.sum_univ_four]
  nlinarith only [h₀, h₁, h₂, h₃, h1,
    Nat.mul_le_mul_right
      (((A.first 0).size + (A.second 0).size) + ((A.first 1).size + (A.second 1).size) +
        ((A.first 2).size + (A.second 2).size) + ((A.first 3).size + (A.second 3).size) + 1) hm]

def source {n : ℕ} (D : CompressionData n) (e : Equiv.Perm (Fin n)) : Arrays :=
  ⟨fun i => (D.storedFirst e i).toArray, fun i => (D.storedSecond e i).toArray⟩

theorem source_value {n : ℕ} (D : CompressionData n) (e : Equiv.Perm (Fin n))
    (q : CompressionSetup.PrimeSpace n) (z : Fin q.val) :
    (prepare (source D e) q.val D.input.target z.val
      (by exact_mod_cast (primeRange_prime q.property).pos)).1 = D.passData e q z := by
  simp only [prepare, CompressionContext.build_value, source, CompressionData.passData,
    CompressionData.storedRightArray, CompressionData.groupStart, CompressionData.streamLength,
    List.size_toArray]

theorem source_sizes {n : ℕ} (D : CompressionData n) (e : Equiv.Perm (Fin n))
    (he : D.compactTests e = true) (hn : 10000 ≤ n) :
    (∀ i, ((source D e).first i).size ≤ 2 ^ n) ∧
      (∀ i, ((source D e).second i).size ≤ 2 ^ n) := by
  have hc : compressionDictionaryCapacity n ≤ 2 ^ n := by
    unfold compressionDictionaryCapacity
    exact Nat.pow_le_pow_right (by decide) (by omega)
  constructor
  · intro i
    exact ((D.stored_lists_capacity e he (by omega) i).1.trans hc)
  · intro i
    exact ((D.stored_lists_capacity e he (by omega) i).2.trans hc)

end LowSpaceSubsetSum.PreparedCompressionPass

end OAI
