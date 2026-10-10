import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionStreams

namespace OAI

/-!
# The compressed trial at its designated solution residue

Both joins below use the concrete shared-array modular streams. Fuel comes
from products of stored-list lengths, so computing it does not enumerate a
Cartesian product. The ideal experiment still uses the proved uniform
permutation and prime law; bounded-sampler and watchdog losses are separate.
-/

namespace LowSpaceSubsetSum.CompressionSetup

variable {n : ℕ} (R : CompressionSetup n)

def streamLength (e : Equiv.Perm (Fin n)) (i : Fin 4) : ℕ :=
  (R.storedFirst e i).length * (R.storedSecond e i).length

theorem initial_output_length (e : Equiv.Perm (Fin n)) (q : PrimeSpace n)
    (i : Fin 4) (mode : FilteredStream.Mode) :
    (R.groupOutput e q i mode (R.groupStart e q i mode)).length = R.streamLength e i := by
  rw [R.groupOutput_length, groupList, pairSumList_length]
  rfl

def actualLeftDictionary (B : ℕ) (e : Equiv.Perm (Fin n)) (q : PrimeSpace n)
    (z : Fin q.val) : BinaryTrie.BuildResult :=
  (StreamJoin.run (R.groupRead e q 0 .direct) (fun x => x % (q.val : ℤ))
    (R.groupRead e q 1 (.complementary z.val)) (fun y => ((z.val : ℤ) - y) % q.val)
    (BinaryTrie.callback (compressionDictionaryCapacity n)
      (fun x y => WeightEncoding.weightKey R.input (x + y)))
    B (R.streamLength e 0) (R.streamLength e 1) (R.streamLength e 0 + R.streamLength e 1 + 1)
    (R.groupStart e q 0 .direct) (R.groupStart e q 1 (.complementary z.val))
    ⟨.empty, false, 0⟩).user

theorem actualLeftDictionary_fits (B : ℕ) (e : Equiv.Perm (Fin n)) (q : PrimeSpace n)
    (hq : R.BucketFits e q) :
    (R.actualLeftDictionary B e q (R.solutionResidue e q)).overflow = false ∧
      BinaryTrie.contains (R.actualLeftDictionary B e q (R.solutionResidue e q)).tree
        (WeightEncoding.weightKey R.input (R.leftWeight e)) = true := by
  apply R.generated_left_dictionary e q hq
    (R.groupRead e q 0 .direct) (R.groupRead e q 1 (.complementary (R.solutionResidue e q).val))
    (R.groupOutput e q 0 .direct) (R.groupRead_law e q 0 .direct)
    (R.groupOutput e q 1 (.complementary (R.solutionResidue e q).val))
    (R.groupRead_law e q 1 (.complementary (R.solutionResidue e q).val))
    (R.groupStart e q 0 .direct) (R.groupStart e q 1 (.complementary (R.solutionResidue e q).val))
    (R.groupOutput_mem e q 0 .direct) (R.groupOutput_mem e q 1 (.complementary _))
    B (R.streamLength e 0) (R.streamLength e 1) (R.streamLength e 0 + R.streamLength e 1 + 1)
  · exact R.groupOutput_sorted e q 0 .direct
  · exact R.groupOutput_sorted e q 1 (.complementary _)
  · exact (R.initial_output_length e q 0 .direct).le
  · exact (R.initial_output_length e q 1 (.complementary _)).le
  · rw [R.initial_output_length, R.initial_output_length]
    omega

def actualRightHit (B : ℕ) (e : Equiv.Perm (Fin n)) (q : PrimeSpace n)
    (z : Fin q.val) (tree : BinaryTrie.Tree) : Bool :=
  let target := (R.input.target : ℤ) - z.val
  (StreamJoin.run (R.groupRead e q 2 .direct) (fun x => x % (q.val : ℤ))
    (R.groupRead e q 3 (.complementary target)) (fun y => (target - y) % q.val)
    (StreamWitness.remember (fun x y => BinaryTrie.contains tree
      (WeightEncoding.weightKey R.input ((R.input.target : ℤ) - (x + y)))))
    B (R.streamLength e 2) (R.streamLength e 3) (R.streamLength e 2 + R.streamLength e 3 + 1)
    (R.groupStart e q 2 .direct) (R.groupStart e q 3 (.complementary target)) false).user

theorem actualRightHit_true (B : ℕ) (e : Equiv.Perm (Fin n)) (q : PrimeSpace n)
    (tree : BinaryTrie.Tree)
    (hleft : BinaryTrie.contains tree (WeightEncoding.weightKey R.input (R.leftWeight e)) = true) :
    R.actualRightHit B e q (R.solutionResidue e q) tree = true := by
  apply R.generated_right_hit e q tree hleft
    (R.groupRead e q 2 .direct)
    (R.groupRead e q 3 (.complementary ((R.input.target : ℤ) - (R.solutionResidue e q).val)))
    (R.groupOutput e q 2 .direct) (R.groupRead_law e q 2 .direct)
    (R.groupOutput e q 3 (.complementary ((R.input.target : ℤ) - (R.solutionResidue e q).val)))
    (R.groupRead_law e q 3 (.complementary _))
    (R.groupStart e q 2 .direct) (R.groupStart e q 3 (.complementary _))
    (R.groupOutput_mem e q 2 .direct) (R.groupOutput_mem e q 3 (.complementary _))
    B (R.streamLength e 2) (R.streamLength e 3) (R.streamLength e 2 + R.streamLength e 3 + 1)
  · exact R.groupOutput_sorted e q 2 .direct
  · exact R.groupOutput_sorted e q 3 (.complementary _)
  · exact (R.initial_output_length e q 2 .direct).le
  · exact (R.initial_output_length e q 3 (.complementary _)).le
  · rw [R.initial_output_length, R.initial_output_length]
    omega

/-- Integer division computes the rational floor used by the size test. -/
def executableCapExponent (n : ℕ) : ℕ :=
  (((400 : ℤ) * ((mixerSize n / 2 : ℕ) : ℤ) - 3 * n) / 400).toNat

theorem executableCapExponent_eq (n : ℕ) :
    executableCapExponent n = compressionCapExponent n := by
  unfold executableCapExponent compressionCapExponent
  rw [← Int.floor_toNat]
  congr 1
  have heq : ((mixerSize n / 2 : ℕ) : ℝ) - (3 / 400 : ℝ) * n =
      (((400 : ℤ) * ((mixerSize n / 2 : ℕ) : ℤ) - 3 * n : ℤ) : ℝ) / (400 : ℕ) := by
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat, Nat.cast_ofNat]
    ring
  rw [heq, Int.floor_div_natCast, Int.floor_intCast]
  rfl

def compactTests (e : Equiv.Perm (Fin n)) : Bool :=
  decide (∀ i : Fin 7, (compactWeightList R.weights (R.block e i)).length ≤
    2 ^ executableCapExponent n)

theorem compactTests_iff (e : Equiv.Perm (Fin n)) :
    R.compactTests e = true ↔ R.Passing e := by
  simp only [compactTests, decide_eq_true_eq, compactWeightList_length,
    Passing, distinctSumCount, blockWeights, executableCapExponent_eq]

/-- One explicitly selected residue pass, using concrete streams and tries. -/
def residuePass (B : ℕ) (e : Equiv.Perm (Fin n)) (q : PrimeSpace n)
    (z : Fin q.val) : Bool :=
  if R.compactTests e then
    let dictionary := R.actualLeftDictionary B e q z
    if dictionary.overflow then false else R.actualRightHit B e q z dictionary.tree
  else false

/-- The fixed solution chooses this residue only in the success analysis. -/
def designatedPass (B : ℕ) (e : Equiv.Perm (Fin n)) (q : PrimeSpace n) : Bool :=
  R.residuePass B e q (R.solutionResidue e q)

theorem designatedPass_true (B : ℕ) (e : Equiv.Perm (Fin n)) (q : PrimeSpace n)
    (he : R.Passing e) (hq : R.BucketFits e q) : R.designatedPass B e q = true := by
  have ht := (R.compactTests_iff e).mpr he
  have hd := R.actualLeftDictionary_fits B e q hq
  simp only [designatedPass, residuePass, ht, ↓reduceIte, hd.1, Bool.false_eq_true]
  exact R.actualRightHit_true B e q _ hd.2

theorem designatedPass_probability (B : ℕ) (hn : 168000000 ≤ n)
    (hmean : (153 / 20000 : ℝ) * n ≤
      meanDeficiency R.weights Finset.univ (compressionHalfSize n))
    (hlog : Real.logb 2 (inputScale R.input) ≤ (n : ℝ) / 1000000000) :
    (1 / 4 : ℝ) ≤ (R.trialLaw hn).probability (fun h => R.designatedPass B h.1 h.2 = true) := by
  apply (R.successful_probability hn hmean hlog).trans
  apply FiniteLaw.probability_mono
  intro h hh
  exact R.designatedPass_true B h.1 h.2 hh.1 hh.2

/-- Tail-recursive, constant-state enumeration of a consecutive residue range. -/
def residueLoop (test : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, start => if test start then true else residueLoop test fuel (start + 1)

theorem residueLoop_true_iff (test : ℕ → Bool) (fuel start : ℕ) :
    residueLoop test fuel start = true ↔ ∃ j < fuel, test (start + j) = true := by
  induction fuel generalizing start with
  | zero => simp [residueLoop]
  | succ fuel ih =>
    rw [residueLoop]
    by_cases ht : test start = true
    · simp only [ht, ↓reduceIte, true_iff]
      exact ⟨0, Nat.zero_lt_succ _, by simpa using ht⟩
    · simp only [ht, Bool.false_eq_true, ↓reduceIte, ih]
      constructor
      · rintro ⟨j, hj, hv⟩
        exact ⟨j + 1, by omega, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hv⟩
      · rintro ⟨j, hj, hv⟩
        have hj0 : 0 < j := by
          by_contra h
          have : j = 0 := by omega
          simp_all
        refine ⟨j - 1, by omega, ?_⟩
        convert hv using 1
        congr 1
        omega

/-- The actual compression trial scans every residue; it never uses the solution. -/
def compressionTrial (B : ℕ) (e : Equiv.Perm (Fin n)) (q : PrimeSpace n) : Bool :=
  residueLoop (fun z => if h : z < q.val then R.residuePass B e q ⟨z, h⟩ else false)
    q.val 0

theorem compressionTrial_true_iff (B : ℕ) (e : Equiv.Perm (Fin n)) (q : PrimeSpace n) :
    R.compressionTrial B e q = true ↔ ∃ z : Fin q.val, R.residuePass B e q z = true := by
  rw [compressionTrial, residueLoop_true_iff]
  simp only [Nat.zero_add]
  constructor
  · rintro ⟨z, hz, hv⟩
    exact ⟨⟨z, hz⟩, by simpa only [dite_eq_left hz] using hv⟩
  · rintro ⟨z, hz⟩
    exact ⟨z.val, z.isLt, by simpa only [dite_eq_left z.isLt] using hz⟩

theorem compressionTrial_true (B : ℕ) (e : Equiv.Perm (Fin n)) (q : PrimeSpace n)
    (he : R.Passing e) (hq : R.BucketFits e q) : R.compressionTrial B e q = true :=
  (R.compressionTrial_true_iff B e q).mpr
    ⟨R.solutionResidue e q, R.designatedPass_true B e q he hq⟩

theorem compressionTrial_probability (B : ℕ) (hn : 168000000 ≤ n)
    (hmean : (153 / 20000 : ℝ) * n ≤
      meanDeficiency R.weights Finset.univ (compressionHalfSize n))
    (hlog : Real.logb 2 (inputScale R.input) ≤ (n : ℝ) / 1000000000) :
    (1 / 4 : ℝ) ≤ (R.trialLaw hn).probability (fun h => R.compressionTrial B h.1 h.2 = true) := by
  apply (R.successful_probability hn hmean hlog).trans
  apply FiniteLaw.probability_mono
  intro h hh
  exact R.compressionTrial_true B h.1 h.2 hh.1 hh.2

end LowSpaceSubsetSum.CompressionSetup

end OAI
