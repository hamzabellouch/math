import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionQueryBounds

namespace OAI

/-! # A complete compression-join ledger and its live data structures

The counters retain the actual compact-test and overflow branches. The
storage bound describes the arrays, current cursors, replay snapshots, tie
buffer and bounded trie.
-/

noncomputable section

namespace LowSpaceSubsetSum

open scoped BigOperators

structure CompressionLedger where
  queries : ℕ
  reports : ℕ
  copies : ℕ
  controls : ℕ

namespace CompressionData

variable {n : ℕ} (D : CompressionData n)

/-- No right-hand work is counted after dictionary overflow. The control
count includes even the unused fuel suffix of the original `run` loop. -/
def residueLedger (B : ℕ) (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n)
    (z : Fin q.val) : CompressionLedger :=
  if D.compactTests e then
    let lf := D.streamLength e 0 + D.streamLength e 1 + 1
    let left := D.leftJoin B e q z lf
    if left.user.overflow then
      ⟨left.queries, left.reports, left.copies, lf⟩
    else
      let rf := D.streamLength e 2 + D.streamLength e 3 + 1
      let right := D.rightJoin B e q z left.user.tree rf
      ⟨left.queries + right.queries, left.reports + right.reports,
        left.copies + right.copies, lf + rf⟩
  else ⟨0, 0, 0, 0⟩

def trialLedger (B : ℕ) (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n) :
    CompressionLedger :=
  ⟨∑ z, (D.residueLedger B e q z).queries,
    ∑ z, (D.residueLedger B e q z).reports,
    ∑ z, (D.residueLedger B e q z).copies,
    ∑ z, (D.residueLedger B e q z).controls⟩

theorem residueLedger_queries (B : ℕ) (e : Equiv.Perm (Fin n))
    (q : CompressionSetup.PrimeSpace n) (z : Fin q.val) :
    (D.residueLedger B e q z).queries = D.residueQueries B e q z := by
  simp only [residueLedger, residueQueries]
  split
  · split <;> rfl
  · rfl

theorem residueLedger_bounds (B : ℕ) (e : Equiv.Perm (Fin n))
    (q : CompressionSetup.PrimeSpace n) (z : Fin q.val) :
    (D.residueLedger B e q z).reports ≤ D.leftPotential e q z + D.rightPotential e q z ∧
    B * (D.residueLedger B e q z).copies ≤ 2 * (D.leftPotential e q z + D.rightPotential e q z) ∧
    (D.residueLedger B e q z).controls ≤ (∑ i : Fin 4, D.streamLength e i) + 2 := by
  have hl := D.leftJoin_bounds B e q z (D.streamLength e 0 + D.streamLength e 1 + 1)
  have hr := D.rightJoin_bounds B e q z
    (D.leftJoin B e q z (D.streamLength e 0 + D.streamLength e 1 + 1)).user.tree
    (D.streamLength e 2 + D.streamLength e 3 + 1)
  simp only [residueLedger]
  split
  · split <;> dsimp only
    · simp only [Fin.sum_univ_four]
      omega
    · simp only [Nat.mul_add, Fin.sum_univ_four]
      omega
  · simp

theorem trialLedger_reports_copies (B : ℕ) (e : Equiv.Perm (Fin n))
    (q : CompressionSetup.PrimeSpace n) :
    (D.trialLedger B e q).reports ≤
      D.streamLength e 0 * D.streamLength e 1 + D.streamLength e 2 * D.streamLength e 3 ∧
    B * (D.trialLedger B e q).copies ≤
      2 * (D.streamLength e 0 * D.streamLength e 1 + D.streamLength e 2 * D.streamLength e 3) ∧
    (D.trialLedger B e q).controls ≤ q.val * (∑ i : Fin 4, D.streamLength e i) + 2 * q.val := by
  have hr := Finset.sum_le_sum (fun z (_ : z ∈ (Finset.univ : Finset (Fin q.val))) =>
    (D.residueLedger_bounds B e q z).1)
  have hc := Finset.sum_le_sum (fun z (_ : z ∈ (Finset.univ : Finset (Fin q.val))) =>
    (D.residueLedger_bounds B e q z).2.1)
  have ht := Finset.sum_le_sum (fun z (_ : z ∈ (Finset.univ : Finset (Fin q.val))) =>
    (D.residueLedger_bounds B e q z).2.2)
  simp only [Finset.sum_add_distrib, D.sum_leftPotential, D.sum_rightPotential] at hr
  simp_rw [Nat.mul_add] at hc
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    D.sum_leftPotential, D.sum_rightPotential] at hc
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at ht
  exact ⟨hr, by simpa only [trialLedger, Nat.mul_add] using hc,
    by simpa only [trialLedger, Nat.mul_add, Nat.add_mul, Nat.mul_comm] using ht⟩

/-- A compact bound for all measured join activity in one compression
trial. Copy work is measured in units of a full `B`-word snapshot. -/
theorem trialLedger_half_exponential (B : ℕ) (e : Equiv.Perm (Fin n))
    (q : CompressionSetup.PrimeSpace n) (hn : 2000 ≤ n) :
    ((D.trialLedger B e q).queries : ℝ) ≤ 30 * (2 : ℝ) ^ ((n : ℝ) / 2) ∧
    ((D.trialLedger B e q).reports : ℝ) ≤ 2 * (2 : ℝ) ^ ((n : ℝ) / 2) ∧
    (B * (D.trialLedger B e q).copies : ℕ) ≤ 4 * (2 : ℝ) ^ ((n : ℝ) / 2) ∧
    ((D.trialLedger B e q).controls : ℝ) ≤ 6 * (2 : ℝ) ^ ((n : ℝ) / 2) := by
  have hquery := D.queries_half_exponential B e q hn
  have heq : (D.trialLedger B e q).queries = ∑ z, D.residueQueries B e q z := by
    simp only [trialLedger, D.residueLedger_queries]
  rw [heq]
  refine ⟨by simpa only [Nat.cast_sum] using hquery, ?_⟩
  by_cases he : D.compactTests e = true
  · have h := D.trialLedger_reports_copies B e q
    have hp := D.matching_product_bound e he hn
    have hs : ((q.val * ∑ i : Fin 4, D.streamLength e i : ℕ) : ℝ) ≤
        4 * (2 : ℝ) ^ ((n : ℝ) / 2) := by
      rw [Finset.mul_sum, Nat.cast_sum]
      apply (Finset.sum_le_sum (fun i _ => D.prime_regeneration_bound e he hn q i)).trans_eq
      simp
    have hq : (q.val : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 2) := by
      have hz : 1 ≤ D.streamLength e 0 := by
        have hnonempty (i : Fin 7) : 0 < (compactWeightList D.weights (D.block e i)).length := by
          rw [compactWeightList_length]
          exact Nat.zero_lt_of_lt (Finset.card_pos.mpr ⟨0, zero_mem_distinctSums _ _⟩)
        have h0 := hnonempty 4
        have h1 := hnonempty 5
        change 1 ≤ (compactWeightList D.weights (D.block e 4)).length *
          (compactWeightList D.weights (D.block e 5)).length
        nlinarith
      exact (Nat.cast_le.mpr (Nat.le_mul_of_pos_right _ (by omega))).trans
        (D.prime_regeneration_bound e he hn q 0)
    have hr : ((D.trialLedger B e q).reports : ℝ) ≤
        (D.streamLength e 0 * D.streamLength e 1 : ℕ) +
          (D.streamLength e 2 * D.streamLength e 3 : ℕ) := by exact_mod_cast h.1
    have hc : ((B * (D.trialLedger B e q).copies : ℕ) : ℝ) ≤
        2 * ((D.streamLength e 0 * D.streamLength e 1 : ℕ) +
          (D.streamLength e 2 * D.streamLength e 3 : ℕ)) := by exact_mod_cast h.2.1
    have ht : ((D.trialLedger B e q).controls : ℝ) ≤
        (q.val * ∑ i : Fin 4, D.streamLength e i : ℕ) + 2 * (q.val : ℝ) := by
      exact_mod_cast h.2.2
    exact ⟨by linarith [hp.1, hp.2], by linarith [hp.1, hp.2], by linarith⟩
  · have hf : D.compactTests e = false := Bool.eq_false_iff.mpr he
    simp only [trialLedger, residueLedger, hf, Bool.false_eq_true, ↓reduceIte,
      Finset.sum_const_zero, Nat.mul_zero, Nat.cast_zero]
    exact ⟨by positivity, by positivity, by positivity⟩

/-- Only the mutable tournament and its cached cursors are copied. The
immutable stored arrays are shared by every replay snapshot. -/
def snapshotCells (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n)
    (i : Fin 4) (mode : FilteredStream.Mode) (s : D.GroupState e q i mode) : ℕ :=
  10 * (Tournament.nodes s.tree + 1)

theorem snapshotCells_le_buffer (e : Equiv.Perm (Fin n)) (he : D.compactTests e = true)
    (hn : 2000 ≤ n) (q : CompressionSetup.PrimeSpace n) (i : Fin 4)
    (mode : FilteredStream.Mode) (s : D.GroupState e q i mode) :
    D.snapshotCells e q i mode s ≤ 2 ^ (19 * n / 100) := by
  have ha := compression_cap_rate (by omega : 40 ≤ n)
  have hfloor : 19 * n < 100 * (19 * n / 100 + 1) := by omega
  have hfloorR : (19 : ℝ) * n < 100 * ((19 * n / 100 : ℕ) + 1 : ℝ) := by
    exact_mod_cast hfloor
  have hnR : (2000 : ℝ) ≤ n := by exact_mod_cast hn
  have hexp : compressionCapExponent n + 7 ≤ 19 * n / 100 := by
    have hR : (compressionCapExponent n : ℝ) + 7 ≤ (19 * n / 100 : ℕ) := by linarith
    exact_mod_cast hR
  have ht := Tournament.padded_nodes_le (D.storedFirst e i).toArray.size s.tree
  simp only [List.size_toArray] at ht
  have hl := D.storedFirst_length_bound e he i
  have hpos : 1 ≤ 2 ^ compressionCapExponent n := Nat.one_le_pow _ _ (by decide)
  calc
    D.snapshotCells e q i mode s ≤ 80 * 2 ^ compressionCapExponent n := by
      unfold snapshotCells
      omega
    _ ≤ 2 ^ (compressionCapExponent n + 7) := by
      rw [pow_add]
      norm_num
      omega
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hexp

/-- A conservative simultaneous footprint, including the preliminary
single-block enumeration and three copies of every group state. -/
def storageCells (B : ℕ) (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n)
    (z : Fin q.val) (fuel : ℕ) (mode : Fin 4 → FilteredStream.Mode)
    (states : ∀ i, D.GroupState e q i (mode i)) : ℕ :=
  2 ^ compressionHalfSize n + 7 * 2 ^ compressionCapExponent n +
    3 * (∑ i, D.groupFootprint e q i (mode i) (states i)) + 10 * (B + 1) +
    3 * BinaryTrie.nodes (D.leftJoin B e q z fuel).user.tree

theorem storageCells_bound (B : ℕ) (hB : B ≤ compressionDictionaryCapacity n)
    (e : Equiv.Perm (Fin n)) (he : D.compactTests e = true) (hn : 2000 ≤ n)
    (q : CompressionSetup.PrimeSpace n) (z : Fin q.val) (fuel : ℕ)
    (mode : Fin 4 → FilteredStream.Mode) (states : ∀ i, D.GroupState e q i (mode i)) :
    D.storageCells B e q z fuel mode states ≤
      (800 + 3 * (WeightEncoding.weightWidth D.input + 1)) * (compressionDictionaryCapacity n + 1) := by
  have hs : (∑ i, D.groupFootprint e q i (mode i) (states i)) ≤
      40 * (6 * compressionDictionaryCapacity n + 4) := by
    apply (Finset.sum_le_sum (fun i _ => D.groupFootprint_bound e he hn q i (mode i) (states i))).trans_eq
    simp
    ring
  have ht := D.leftJoin_nodes B e q z fuel
  have hnR : (2000 : ℝ) ≤ n := by exact_mod_cast hn
  have hlow : (2 : ℝ) ^ ((3 / 25 : ℝ) * n) ≤ compressionDictionaryCapacity n := by
    apply (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (show (3 / 25 : ℝ) * n ≤ (199 / 1000 : ℝ) * n - 1 by linarith)).trans
    exact compression_capacity_lower n
  have hhalf : 2 ^ compressionHalfSize n ≤ compressionDictionaryCapacity n := by
    have hb := (mixerSize_bounds n).2
    have hhalfR : (compressionHalfSize n : ℝ) ≤ (3 / 25 : ℝ) * n := by
      have heq : mixerSize n = 2 * compressionHalfSize n := by
        rw [compressionHalfSize_eq]
        unfold mixerSize
        omega
      rw [heq, Nat.cast_mul, Nat.cast_ofNat] at hb
      linarith
    have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hhalfR
    rw [Real.rpow_natCast] at hpow
    exact_mod_cast hpow.trans hlow
  have hcap : 2 ^ compressionCapExponent n ≤ compressionDictionaryCapacity n := by
    have ha := compression_cap_rate (by omega : 40 ≤ n)
    have hrate : (compressionCapExponent n : ℝ) ≤ (3 / 25 : ℝ) * n := by linarith
    have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hrate
    rw [Real.rpow_natCast] at hpow
    exact_mod_cast hpow.trans hlow
  unfold storageCells
  nlinarith only [hs, ht, hhalf, hcap, hB]

end CompressionData
end LowSpaceSubsetSum

end

end OAI
