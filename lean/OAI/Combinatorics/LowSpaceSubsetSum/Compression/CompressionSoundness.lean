import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionProgram
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.DictionaryProvenance

namespace OAI

/-! # One-sided soundness of compression on every input and family outcome -/

namespace LowSpaceSubsetSum.CompressionData

variable {n : ℕ} (D : CompressionData n)

theorem actualLeftDictionary_provenance (B : ℕ) (e : Equiv.Perm (Fin n))
    (q : CompressionSetup.PrimeSpace n) (z : Fin q.val) (query : List Bool)
    (hq : BinaryTrie.contains (D.actualLeftDictionary B e q z).tree query = true) :
    ∃ w ∈ (D.zeroSetup).leftWeights e, WeightEncoding.weightKey D.input w = query := by
  have hp := BinaryTrie.join_provenance
    (C := compressionDictionaryCapacity n) (width := WeightEncoding.weightWidth D.input)
    (D.groupRead e q 0 .direct) (fun x => x % (q.val : ℤ))
    (D.groupRead e q 1 (.complementary z.val)) (fun y => ((z.val : ℤ) - y) % q.val)
    (fun x y => WeightEncoding.weightKey D.input (x + y))
    (D.groupOutput e q 0 .direct) (D.groupRead_law e q 0 .direct)
    (D.groupOutput e q 1 (.complementary z.val)) (D.groupRead_law e q 1 (.complementary z.val))
    B (D.streamLength e 0) (D.streamLength e 1) (D.streamLength e 0 + D.streamLength e 1 + 1)
    (D.groupStart e q 0 .direct) (D.groupStart e q 1 (.complementary z.val))
    (D.groupOutput_sorted e q 0 .direct) (D.groupOutput_sorted e q 1 (.complementary z.val))
    (by rw [D.initial_output_length]) (by rw [D.initial_output_length])
    (by rw [D.initial_output_length, D.initial_output_length]; omega)
    (fun x _ y _ _ => WeightEncoding.weightKey_length D.input (x + y)) query hq
  obtain ⟨x, hx, y, hy, _, he⟩ := hp
  have hx' := ((D.zeroSetup).mem_groupList e 0 x).mpr
    ((D.groupOutput_mem e q 0 .direct x).mp hx)
  have hy' := ((D.zeroSetup).mem_groupList e 1 y).mpr
    ((D.groupOutput_mem e q 1 (.complementary z.val) y).mp hy)
  exact ⟨x + y, (D.zeroSetup).leftPair_mem e hx' hy', he⟩

theorem rightPair_mem (e : Equiv.Perm (Fin n)) {x y : ℤ}
    (hx : x ∈ (D.zeroSetup).groupWeights e 2) (hy : y ∈ (D.zeroSetup).groupWeights e 3) :
    x + y ∈ (D.zeroSetup).rightWeights e := by
  change x + y ∈ distinctSums _ _
  rw [(D.zeroSetup).rightDomain_eq_groups]
  exact (distinctSums_union_mem_iff _ _ _ ((D.zeroSetup).right_groups_disjoint e) _).mpr
    ⟨x, hx, y, hy, rfl⟩

theorem actualRightHit_provenance (B : ℕ) (e : Equiv.Perm (Fin n))
    (q : CompressionSetup.PrimeSpace n) (z : Fin q.val) (tree : BinaryTrie.Tree)
    (hyes : D.actualRightHit B e q z tree = true) :
    ∃ w ∈ (D.zeroSetup).rightWeights e,
      BinaryTrie.contains tree (WeightEncoding.weightKey D.input ((D.input.target : ℤ) - w)) = true := by
  let target := (D.input.target : ℤ) - z.val
  have hp := StreamWitness.stopped_sound
    (D.groupRead e q 2 .direct) (fun x => x % (q.val : ℤ))
    (D.groupRead e q 3 (.complementary target)) (fun y => (target - y) % q.val)
    (fun x y => BinaryTrie.contains tree (WeightEncoding.weightKey D.input
      ((D.input.target : ℤ) - (x + y))))
    (D.groupOutput e q 2 .direct) (D.groupRead_law e q 2 .direct)
    (D.groupOutput e q 3 (.complementary target)) (D.groupRead_law e q 3 (.complementary target))
    B (D.streamLength e 2) (D.streamLength e 3) (D.streamLength e 2 + D.streamLength e 3 + 1)
    (D.groupStart e q 2 .direct) (D.groupStart e q 3 (.complementary target))
    (D.groupOutput_sorted e q 2 .direct) (D.groupOutput_sorted e q 3 (.complementary target))
    (by rw [D.initial_output_length]) (by rw [D.initial_output_length]) hyes
  obtain ⟨x, hx, y, hy, _, hhit⟩ := hp
  exact ⟨x + y, D.rightPair_mem e ((D.groupOutput_mem e q 2 .direct x).mp hx)
    ((D.groupOutput_mem e q 3 (.complementary target) y).mp hy), hhit⟩

theorem subset_weight_bound (S : Finset (Fin n)) :
    (weight D.weights S).natAbs ≤ n * 2 ^ inputBits D.input := by
  simpa only [Fintype.card_fin] using weight_natAbs_le D.weights S
    (M := 2 ^ inputBits D.input) (fun i => by
      simpa only [weights, Int.natAbs_natCast] using (value_lt_two_pow_bits D.input i).le)

theorem distinct_weight_bound (V : Finset (Fin n)) {w : ℤ} (hw : w ∈ distinctSums D.weights V) :
    w.natAbs ≤ n * 2 ^ inputBits D.input := by
  obtain ⟨S, _, rfl⟩ := (mem_distinctSums _ _ _).mp hw
  exact D.subset_weight_bound S

theorem residuePass_sound (B : ℕ) (e : Equiv.Perm (Fin n))
    (q : CompressionSetup.PrimeSpace n) (z : Fin q.val)
    (hyes : D.residuePass B e q z = true) : Solvable D.input := by
  by_cases htest : D.compactTests e = true
  · simp [residuePass, htest] at hyes
    obtain ⟨r, hr, hhit⟩ := D.actualRightHit_provenance B e q z _ hyes.2
    obtain ⟨l, hl, hkey⟩ := D.actualLeftDictionary_provenance B e q z _ hhit
    have hlb := D.distinct_weight_bound _ hl
    have hrb := D.distinct_weight_bound _ hr
    have htb := (target_lt_two_pow_bits D.input).le
    have hqb := Int.natAbs_sub_le (D.input.target : ℤ) r
    simp only [Int.natAbs_natCast] at hqb
    have heq : l = (D.input.target : ℤ) - r := WeightEncoding.weightKey_injective D.input
      (by unfold WeightEncoding.BoundedWeight; nlinarith)
      (by unfold WeightEncoding.BoundedWeight; nlinarith) hkey
    obtain ⟨L, hL, hwl⟩ := (mem_distinctSums D.weights ((D.zeroSetup).leftDomain e) l).mp hl
    obtain ⟨R, hR, hwr⟩ := (mem_distinctSums D.weights ((D.zeroSetup).rightDomain e) r).mp hr
    have hd : Disjoint L R := by
      apply Finset.disjoint_left.mpr
      intro i hi hj
      have hri : i ∈ Finset.univ \ (D.zeroSetup).leftDomain e := hR hj
      exact (Finset.mem_sdiff.mp hri).2 (hL hi)
    refine ⟨L ∪ R, ?_⟩
    change weight D.weights (L ∪ R) = D.input.target
    rw [weight_union _ hd, hwl, hwr, heq]
    omega
  · simp [residuePass, htest] at hyes

theorem compressionTrial_sound (B : ℕ) (e : Equiv.Perm (Fin n))
    (q : CompressionSetup.PrimeSpace n) (hyes : D.compressionTrial B e q = true) :
    Solvable D.input := by
  rw [compressionTrial, CompressionSetup.residueLoop_true_iff] at hyes
  obtain ⟨z, hz, htest⟩ := hyes
  simp only [Nat.zero_add, dite_eq_left hz] at htest
  exact D.residuePass_sound B e q ⟨z, hz⟩ htest

noncomputable def trialLaw (hn : 168000000 ≤ n) : FiniteLaw (CompressionSetup.TrialHistory n) :=
  (D.zeroSetup).trialLaw hn

theorem compressionTrial_probability (B : ℕ) (hn : 168000000 ≤ n)
    (hsolve : Solvable D.input)
    (hmean : (153 / 20000 : ℝ) * n ≤
      meanDeficiency D.weights Finset.univ (compressionHalfSize n))
    (hlog : Real.logb 2 (inputScale D.input) ≤ (n : ℝ) / 1000000000) :
    (1 / 4 : ℝ) ≤ (D.trialLaw hn).probability (fun h => D.compressionTrial B h.1 h.2 = true) := by
  obtain ⟨S, hS⟩ := hsolve
  let R : CompressionSetup n := ⟨D.input, S, hS⟩
  exact R.compressionTrial_probability B hn hmean hlog

end LowSpaceSubsetSum.CompressionData

end OAI
