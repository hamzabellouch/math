import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionWorkBounds
import OAI.Combinatorics.LowSpaceSubsetSum.Counting.ResidueMatchAccounting
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.DictionaryPrefixes

namespace OAI

/-! # Actual compression join queries across the deterministic residue loop -/

noncomputable section

namespace LowSpaceSubsetSum

open scoped BigOperators

namespace MatchPotential

theorem count_perm {α β : Type*} (k₁ : α → ℤ) (k₂ : β → ℤ)
    {xs xs' : List α} {ys ys' : List β} (hx : xs.Perm xs') (hy : ys.Perm ys') :
    count k₁ k₂ xs ys = count k₁ k₂ xs' ys' := by
  rw [count_eq_filter_product_length, count_eq_filter_product_length]
  exact ((hx.product hy).filter _).length_eq

end MatchPotential

namespace CompressionData

variable {n : ℕ} (D : CompressionData n)

theorem groupOutput_perm (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n)
    (i : Fin 4) (mode : FilteredStream.Mode) :
    (D.groupOutput e q i mode (D.groupStart e q i mode)).Perm (D.groupList e i) := by
  have hp := (FilteredStream.sorted_output_perm
    (D.storedFirst e i).toArray (D.storedSecond e i).toArray id id 1 q.val 0
    (by exact_mod_cast (primeRange_prime q.property).pos) mode).map
      (fun p : ℤ × ℤ => p.1 + p.2)
  simpa only [groupOutput, groupStart, storedRightArray, groupList, pairSumList, id_eq,
    Int.emod_one, decide_true, List.filter_true, List.toList_toArray, SProd.sprod] using hp

def leftJoin (B : ℕ) (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n)
    (z : Fin q.val) (fuel : ℕ) :=
  StreamJoin.run (D.groupRead e q 0 .direct) (fun x => x % (q.val : ℤ))
    (D.groupRead e q 1 (.complementary z.val)) (fun y => ((z.val : ℤ) - y) % q.val)
    (BinaryTrie.callback (compressionDictionaryCapacity n)
      (fun x y => WeightEncoding.weightKey D.input (x + y)))
    B (D.streamLength e 0) (D.streamLength e 1) fuel
    (D.groupStart e q 0 .direct) (D.groupStart e q 1 (.complementary z.val))
    ⟨.empty, false, 0⟩

def rightJoin (B : ℕ) (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n)
    (z : Fin q.val) (tree : BinaryTrie.Tree) (fuel : ℕ) :=
  let target := (D.input.target : ℤ) - z.val
  StreamJoin.run (D.groupRead e q 2 .direct) (fun x => x % (q.val : ℤ))
    (D.groupRead e q 3 (.complementary target)) (fun y => (target - y) % q.val)
    (StreamWitness.remember (fun x y => BinaryTrie.contains tree
      (WeightEncoding.weightKey D.input ((D.input.target : ℤ) - (x + y)))))
    B (D.streamLength e 2) (D.streamLength e 3) fuel
    (D.groupStart e q 2 .direct) (D.groupStart e q 3 (.complementary target)) false

theorem leftJoin_user (B : ℕ) (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n)
    (z : Fin q.val) :
    (D.leftJoin B e q z (D.streamLength e 0 + D.streamLength e 1 + 1)).user =
      D.actualLeftDictionary B e q z := rfl

theorem rightJoin_user (B : ℕ) (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n)
    (z : Fin q.val) (tree : BinaryTrie.Tree) :
    (D.rightJoin B e q z tree (D.streamLength e 2 + D.streamLength e 3 + 1)).user =
      D.actualRightHit B e q z tree := rfl

def leftPotential (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n) (z : Fin q.val) : ℕ :=
  MatchPotential.count (fun x => x % (q.val : ℤ)) (fun y => ((z.val : ℤ) - y) % q.val)
    (D.groupList e 0) (D.groupList e 1)

def rightPotential (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n) (z : Fin q.val) : ℕ :=
  MatchPotential.count (fun x => x % (q.val : ℤ))
    (fun y => ((D.input.target : ℤ) - z.val - y) % q.val)
    (D.groupList e 2) (D.groupList e 3)

theorem leftJoin_bounds (B : ℕ) (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n)
    (z : Fin q.val) (fuel : ℕ) :
    (D.leftJoin B e q z fuel).queries ≤
      6 * (D.streamLength e 0 + D.streamLength e 1) + D.leftPotential e q z + 2 ∧
    (D.leftJoin B e q z fuel).reports ≤ D.leftPotential e q z ∧
    B * (D.leftJoin B e q z fuel).copies ≤ 2 * D.leftPotential e q z := by
  have h := StreamJoin.run_bounds
    (D.groupRead e q 0 .direct) (fun x => x % (q.val : ℤ))
    (D.groupRead e q 1 (.complementary z.val)) (fun y => ((z.val : ℤ) - y) % q.val)
    (BinaryTrie.callback (compressionDictionaryCapacity n)
      (fun x y => WeightEncoding.weightKey D.input (x + y))) (fun _ _ _ => rfl)
    (D.groupOutput e q 0 .direct) (D.groupRead_law e q 0 .direct)
    (D.groupOutput e q 1 (.complementary z.val)) (D.groupRead_law e q 1 (.complementary z.val))
    B (D.streamLength e 0) (D.streamLength e 1) fuel
    (D.groupStart e q 0 .direct) (D.groupStart e q 1 (.complementary z.val)) ⟨.empty, false, 0⟩
    (D.groupOutput_sorted e q 0 .direct) (D.groupOutput_sorted e q 1 (.complementary z.val))
    (by rw [D.initial_output_length]) (by rw [D.initial_output_length])
  have hp := MatchPotential.count_perm
    (fun x => x % (q.val : ℤ)) (fun y => ((z.val : ℤ) - y) % q.val)
    (D.groupOutput_perm e q 0 .direct) (D.groupOutput_perm e q 1 (.complementary z.val))
  simpa only [leftJoin, leftPotential, D.initial_output_length, hp] using h

theorem rightJoin_bounds (B : ℕ) (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n)
    (z : Fin q.val) (tree : BinaryTrie.Tree) (fuel : ℕ) :
    (D.rightJoin B e q z tree fuel).queries ≤
      6 * (D.streamLength e 2 + D.streamLength e 3) + D.rightPotential e q z + 2 ∧
    (D.rightJoin B e q z tree fuel).reports ≤ D.rightPotential e q z ∧
    B * (D.rightJoin B e q z tree fuel).copies ≤ 2 * D.rightPotential e q z := by
  let target := (D.input.target : ℤ) - z.val
  have h := StreamJoin.run_bounds
    (D.groupRead e q 2 .direct) (fun x => x % (q.val : ℤ))
    (D.groupRead e q 3 (.complementary target)) (fun y => (target - y) % q.val)
    (StreamWitness.remember (fun x y => BinaryTrie.contains tree
      (WeightEncoding.weightKey D.input ((D.input.target : ℤ) - (x + y))))) (fun _ _ _ => rfl)
    (D.groupOutput e q 2 .direct) (D.groupRead_law e q 2 .direct)
    (D.groupOutput e q 3 (.complementary target)) (D.groupRead_law e q 3 (.complementary target))
    B (D.streamLength e 2) (D.streamLength e 3) fuel
    (D.groupStart e q 2 .direct) (D.groupStart e q 3 (.complementary target)) false
    (D.groupOutput_sorted e q 2 .direct) (D.groupOutput_sorted e q 3 (.complementary target))
    (by rw [D.initial_output_length]) (by rw [D.initial_output_length])
  have hp := MatchPotential.count_perm
    (fun x => x % (q.val : ℤ)) (fun y => (target - y) % q.val)
    (D.groupOutput_perm e q 2 .direct) (D.groupOutput_perm e q 3 (.complementary target))
  simpa only [rightJoin, rightPotential, target, D.initial_output_length, hp] using h

theorem sum_leftPotential (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n) :
    (∑ z, D.leftPotential e q z) = D.streamLength e 0 * D.streamLength e 1 := by
  have h := ResidueMatchAccounting.sum_potential (primeRange_prime q.property).pos
    id id (D.groupList e 0) (D.groupList e 1)
  simpa only [leftPotential, groupList, pairSumList_length, streamLength, id_eq] using h

theorem sum_rightPotential (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n) :
    (∑ z, D.rightPotential e q z) = D.streamLength e 2 * D.streamLength e 3 := by
  have h := ResidueMatchAccounting.sum_complementary_potential (primeRange_prime q.property).pos
    (D.input.target : ℤ) id id (D.groupList e 2) (D.groupList e 3)
  simpa only [rightPotential, groupList, pairSumList_length, streamLength, id_eq] using h

/-- The query counter of the actually enabled two joins. The right join is
skipped on overflow, and all joins are skipped when a compact-list test fails. -/
def residueQueries (B : ℕ) (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n)
    (z : Fin q.val) : ℕ :=
  if D.compactTests e then
    let left := D.leftJoin B e q z (D.streamLength e 0 + D.streamLength e 1 + 1)
    left.queries + if left.user.overflow then 0 else
      (D.rightJoin B e q z left.user.tree (D.streamLength e 2 + D.streamLength e 3 + 1)).queries
  else 0

theorem residueQueries_le (B : ℕ) (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n)
    (z : Fin q.val) :
    D.residueQueries B e q z ≤ 6 * (∑ i : Fin 4, D.streamLength e i) +
      D.leftPotential e q z + D.rightPotential e q z + 4 := by
  have hl := (D.leftJoin_bounds B e q z (D.streamLength e 0 + D.streamLength e 1 + 1)).1
  have hr := (D.rightJoin_bounds B e q z
    (D.leftJoin B e q z (D.streamLength e 0 + D.streamLength e 1 + 1)).user.tree
    (D.streamLength e 2 + D.streamLength e 3 + 1)).1
  simp only [residueQueries]
  split
  · split <;> simp only [Fin.sum_univ_four] <;> omega
  · omega

theorem sum_residueQueries_le (B : ℕ) (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n) :
    (∑ z, D.residueQueries B e q z) ≤
      6 * (q.val * ∑ i : Fin 4, D.streamLength e i) +
        D.streamLength e 0 * D.streamLength e 1 +
        D.streamLength e 2 * D.streamLength e 3 + 4 * q.val := by
  apply (Finset.sum_le_sum (fun z _ => D.residueQueries_le B e q z)).trans_eq
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    D.sum_leftPotential, D.sum_rightPotential]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

theorem queries_half_exponential (B : ℕ) (e : Equiv.Perm (Fin n))
    (q : CompressionSetup.PrimeSpace n) (hn : 2000 ≤ n) :
    ((∑ z, D.residueQueries B e q z) : ℝ) ≤ 30 * (2 : ℝ) ^ ((n : ℝ) / 2) := by
  by_cases he : D.compactTests e = true
  · have hs : ((q.val * ∑ i : Fin 4, D.streamLength e i : ℕ) : ℝ) ≤
        4 * (2 : ℝ) ^ ((n : ℝ) / 2) := by
      rw [Finset.mul_sum, Nat.cast_sum]
      apply (Finset.sum_le_sum (fun i _ => D.prime_regeneration_bound e he hn q i)).trans_eq
      simp
    have hp := D.matching_product_bound e he hn
    have hq : (q.val : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 2) := by
      have hq' : q.val ≤ 2 ^ compressionPrimeExponent n :=
        Nat.le_of_mem_primesLE (Finset.mem_filter.mp q.property).1
      apply (Nat.cast_le.mpr hq').trans
      rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hfloor : 1000 * compressionPrimeExponent n ≤ 249 * n := by
        unfold compressionPrimeExponent
        omega
      have hR : (1000 : ℝ) * compressionPrimeExponent n ≤ 249 * n := by exact_mod_cast hfloor
      linarith
    have hledger : ((∑ z, D.residueQueries B e q z) : ℝ) ≤
        6 * (q.val * ∑ i : Fin 4, D.streamLength e i : ℕ) +
          (D.streamLength e 0 * D.streamLength e 1 : ℕ) +
          (D.streamLength e 2 * D.streamLength e 3 : ℕ) + 4 * (q.val : ℝ) := by
      exact_mod_cast D.sum_residueQueries_le B e q
    linarith [hp.1, hp.2]
  · have hf : D.compactTests e = false := Bool.eq_false_iff.mpr he
    simp only [residueQueries, hf, Bool.false_eq_true, ↓reduceIte, Finset.sum_const_zero, Nat.cast_zero]
    positivity

/-- Capacity is respected even at arbitrary stopped control prefixes. -/
theorem leftJoin_nodes (B : ℕ) (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n)
    (z : Fin q.val) (fuel : ℕ) :
    BinaryTrie.nodes (D.leftJoin B e q z fuel).user.tree ≤
      (WeightEncoding.weightWidth D.input + 1) * (compressionDictionaryCapacity n + 1) := by
  exact DictionaryPrefixes.stopped_nodes
    (D.groupRead e q 0 .direct) (fun x => x % (q.val : ℤ))
    (D.groupRead e q 1 (.complementary z.val)) (fun y => ((z.val : ℤ) - y) % q.val)
    (fun x y => WeightEncoding.weightKey D.input (x + y))
    (fun x y => WeightEncoding.weightKey_length D.input (x + y))
    B (D.streamLength e 0) (D.streamLength e 1) fuel
    (D.groupStart e q 0 .direct) (D.groupStart e q 1 (.complementary z.val))

end CompressionData
end LowSpaceSubsetSum

end

end OAI
