import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionTrial

namespace OAI

/-!
# Compression runtime on arbitrary inputs

The runtime data contains only the input. In particular, neither a fixed
solution nor evidence of solvability is available to the executable scan.
A fixed solution is used only to analyze the success probability of the
input-only scan.
-/

namespace LowSpaceSubsetSum

structure CompressionData (n : ℕ) where
  input : Instance n

namespace CompressionData

variable {n : ℕ} (D : CompressionData n)

def weights : Fin n → ℤ := fun i => D.input.values i
def block (_D : CompressionData n) (e : Equiv.Perm (Fin n)) (i : Fin 7) : Finset (Fin n) :=
  permuteSubset e (compressionBlock n i)
def leftRaw (_D : CompressionData n) (e : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  permuteSubset e (compressionLeftRaw n)
def rightRaw (_D : CompressionData n) (e : Equiv.Perm (Fin n)) (i : Fin 2) : Finset (Fin n) :=
  permuteSubset e (compressionRightRaw n i)

def storedFirst (e : Equiv.Perm (Fin n)) : Fin 4 → List ℤ :=
  ![compactWeightList D.weights (D.block e 4), compactWeightList D.weights (D.block e 6),
    compactWeightList D.weights (D.block e 0), compactWeightList D.weights (D.block e 2)]

def storedSecond (e : Equiv.Perm (Fin n)) : Fin 4 → List ℤ :=
  ![compactWeightList D.weights (D.block e 5), rawWeightList D.weights (D.leftRaw e),
    pairSumList (compactWeightList D.weights (D.block e 1)) (rawWeightList D.weights (D.rightRaw e 0)),
    pairSumList (compactWeightList D.weights (D.block e 3)) (rawWeightList D.weights (D.rightRaw e 1))]

def groupList (e : Equiv.Perm (Fin n)) (i : Fin 4) : List ℤ :=
  pairSumList (D.storedFirst e i) (D.storedSecond e i)

def storedRightArray (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n) (i : Fin 4) : Array ℤ :=
  ResidueSort.sort (D.storedSecond e i).toArray id 1 q.val

abbrev GroupState (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n)
    (i : Fin 4) (mode : FilteredStream.Mode) :=
  MergedReader.State (FilteredStream.key (id : ℤ → ℤ) id q.val mode)
    (FilteredStream.view (α := ℤ) (D.storedRightArray e q i))
    (Nat.clog 2 (D.storedFirst e i).toArray.size)

def groupStart (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n)
    (i : Fin 4) (mode : FilteredStream.Mode) : D.GroupState e q i mode :=
  FilteredStream.sortedStart (D.storedFirst e i).toArray (D.storedSecond e i).toArray
    id id 1 q.val 0 (by exact_mod_cast (primeRange_prime q.property).pos) mode

def groupRead (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n)
    (i : Fin 4) (mode : FilteredStream.Mode) :
    D.GroupState e q i mode → Option (ℤ × D.GroupState e q i mode) :=
  mapReader (fun p : ℤ × ℤ => p.1 + p.2)
    (MergedReader.next (FilteredStream.key id id q.val mode)
      (FilteredStream.read (D.storedRightArray e q i))
      (FilteredStream.view (D.storedRightArray e q i)) (FilteredStream.reader _))

def groupOutput (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n)
    (i : Fin 4) (mode : FilteredStream.Mode) (s : D.GroupState e q i mode) : List ℤ :=
  (MergedReader.output (FilteredStream.key id id q.val mode)
    (FilteredStream.read (D.storedRightArray e q i))
    (FilteredStream.view (D.storedRightArray e q i)) s).map (fun p => p.1 + p.2)

def streamLength (e : Equiv.Perm (Fin n)) (i : Fin 4) : ℕ :=
  (D.storedFirst e i).length * (D.storedSecond e i).length

def actualLeftDictionary (B : ℕ) (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n)
    (z : Fin q.val) : BinaryTrie.BuildResult :=
  (StreamJoin.run (D.groupRead e q 0 .direct) (fun x => x % (q.val : ℤ))
    (D.groupRead e q 1 (.complementary z.val)) (fun y => ((z.val : ℤ) - y) % q.val)
    (BinaryTrie.callback (compressionDictionaryCapacity n)
      (fun x y => WeightEncoding.weightKey D.input (x + y)))
    B (D.streamLength e 0) (D.streamLength e 1) (D.streamLength e 0 + D.streamLength e 1 + 1)
    (D.groupStart e q 0 .direct) (D.groupStart e q 1 (.complementary z.val))
    ⟨.empty, false, 0⟩).user

def actualRightHit (B : ℕ) (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n)
    (z : Fin q.val) (tree : BinaryTrie.Tree) : Bool :=
  let target := (D.input.target : ℤ) - z.val
  (StreamJoin.run (D.groupRead e q 2 .direct) (fun x => x % (q.val : ℤ))
    (D.groupRead e q 3 (.complementary target)) (fun y => (target - y) % q.val)
    (StreamWitness.remember (fun x y => BinaryTrie.contains tree
      (WeightEncoding.weightKey D.input ((D.input.target : ℤ) - (x + y)))))
    B (D.streamLength e 2) (D.streamLength e 3) (D.streamLength e 2 + D.streamLength e 3 + 1)
    (D.groupStart e q 2 .direct) (D.groupStart e q 3 (.complementary target)) false).user

def compactTests (e : Equiv.Perm (Fin n)) : Bool :=
  decide (∀ i : Fin 7, (compactWeightList D.weights (D.block e i)).length ≤
    2 ^ CompressionSetup.executableCapExponent n)

def residuePass (B : ℕ) (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n)
    (z : Fin q.val) : Bool :=
  if D.compactTests e then
    let dictionary := D.actualLeftDictionary B e q z
    if dictionary.overflow then false else D.actualRightHit B e q z dictionary.tree
  else false

def compressionTrial (B : ℕ) (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n) : Bool :=
  CompressionSetup.residueLoop (fun z => if h : z < q.val then D.residuePass B e q ⟨z, h⟩ else false)
    q.val 0

/-- A zero-target analysis wrapper reuses only group-domain facts. Its
empty solution never enters the runtime definitions above. -/
def zeroSetup : CompressionSetup n :=
  ⟨{ D.input with target := 0 }, ∅, by simp⟩

theorem groupRead_law (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n)
    (i : Fin 4) (mode : FilteredStream.Mode) :
    RowMerge.IsReader (D.groupRead e q i mode) (D.groupOutput e q i mode) :=
  (D.zeroSetup).groupRead_law e q i mode

theorem groupOutput_mem (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n)
    (i : Fin 4) (mode : FilteredStream.Mode) (z : ℤ) :
    z ∈ D.groupOutput e q i mode (D.groupStart e q i mode) ↔
      z ∈ (D.zeroSetup).groupWeights e i :=
  ((D.zeroSetup).groupOutput_mem e q i mode z).trans ((D.zeroSetup).mem_groupList e i z)

theorem groupOutput_sorted (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n)
    (i : Fin 4) (mode : FilteredStream.Mode) :
    (D.groupOutput e q i mode (D.groupStart e q i mode)).Pairwise
      (fun x y => CompressionSetup.groupKey q mode x ≤ CompressionSetup.groupKey q mode y) :=
  (D.zeroSetup).groupOutput_sorted e q i mode

theorem initial_output_length (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n)
    (i : Fin 4) (mode : FilteredStream.Mode) :
    (D.groupOutput e q i mode (D.groupStart e q i mode)).length = D.streamLength e i :=
  (D.zeroSetup).initial_output_length e q i mode

end CompressionData

namespace CompressionSetup

variable {n : ℕ} (R : CompressionSetup n)

def runtimeData : CompressionData n := ⟨R.input⟩

theorem runtime_trial_eq (B : ℕ) (e : Equiv.Perm (Fin n)) (q : CompressionSetup.PrimeSpace n) :
    R.runtimeData.compressionTrial B e q = R.compressionTrial B e q := by rfl

end CompressionSetup
end LowSpaceSubsetSum

end OAI
