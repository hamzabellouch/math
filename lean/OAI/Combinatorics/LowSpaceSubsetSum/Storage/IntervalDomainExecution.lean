import OAI.Combinatorics.LowSpaceSubsetSum.Storage.CanonicalMixers
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationMixerPreparation

namespace OAI

/-! # Arithmetic scans for the fixed input-index domains

The actual scan tests two integer inequalities. The Finsets used in the
probability argument are not stored or searched by the executable scan.
Both values and charged work agree with the finite-set domain specification.
-/

namespace LowSpaceSubsetSum.IntervalDomainExecution

open scoped BigOperators
variable {n : ℕ}

def positions (n start len : ℕ) : List (Fin n) :=
  (List.finRange n).filter (fun i => decide (start ≤ i.val ∧ i.val < start + len))

def run (v : Vector (Fin n) n) (start len : ℕ) : List (Fin n) × ℕ :=
  let xs := (positions n start len).map (fun i => v[i.val])
  let sorted := MeasuredSort.sort (fun x y : Fin n => (decide (x ≤ y), 1)) xs
  (sorted.1, sorted.2 + 8 * (n + 1) ^ 2)

theorem positions_source (n start len : ℕ) :
    positions n start len = CompressionDomains.positions (indexInterval n start len) := by
  simp only [positions, CompressionDomains.positions, indexInterval, Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem source (v : Vector (Fin n) n) (start len : ℕ) :
    run v start len = CompressionDomains.domain v (indexInterval n start len) := by
  simp only [run, CompressionDomains.domain, CompressionDomains.unsorted, positions_source]

theorem work (v : Vector (Fin n) n) (start len : ℕ) :
    (run v start len).2 ≤ 40 * (n + 1) ^ 2 := by
  rw [source]
  exact CompressionDomains.domain_work v _

def mixers (I : Instance n) (v : Vector (Fin n) n) :
    RepresentationMixerPreparation.Result n × ℕ :=
  let domains := Vector.ofFn (fun i : Fin 3 => run v (i.val * mixerSize n) (mixerSize n))
  let counts := Vector.ofFn (fun i : Fin 3 =>
    MixerHalfLists.count (fun j => (I.values j : ℤ)) domains[i.val].1)
  (⟨domains.map Prod.fst, counts.map Prod.fst⟩,
    (∑ i : Fin 3, (domains[i.val].2 + counts[i.val].2)) + 12)

theorem mixers_source (I : Instance n) (v : Vector (Fin n) n) :
    mixers I v = RepresentationMixerPreparation.run (canonicalRepresentationData I) v := by
  simp only [mixers, source, RepresentationMixerPreparation.run, canonicalRepresentationData,
    canonicalMixers]

theorem mixers_work (I : Instance n) (hn : 10000 ≤ n) (v : Vector (Fin n) n)
    (e : Equiv.Perm (Fin n)) (hv : ∀ i : Fin n, v[i.val] = e i) :
    (mixers I v).2 ≤ inputScale I ^ 5 * 2 ^ mixerSize n := by
  rw [mixers_source]
  exact RepresentationMixerPreparation.work (canonicalRepresentationData I) hn v e hv

def rightStart (n : ℕ) (i : Fin 2) : ℕ :=
  if i = 0 then n - compressionRightRawSize n
  else n - compressionRightRawSize n + compressionRightRawSize n / 2

def rightLength (n : ℕ) (i : Fin 2) : ℕ :=
  if i = 0 then compressionRightRawSize n / 2
  else compressionRightRawSize n - compressionRightRawSize n / 2

def compression (v : Vector (Fin n) n) : CompressionArrayBuild.Blocks n × ℕ :=
  let compact := Vector.ofFn (fun i : Fin 7 =>
    run v (i.val * compressionHalfSize n) (compressionHalfSize n))
  let left := run v (7 * compressionHalfSize n) (compressionLeftRawSize n)
  let right := Vector.ofFn (fun i : Fin 2 => run v (rightStart n i) (rightLength n i))
  (⟨fun i => compact[i.val].1, left.1, fun i => right[i.val].1⟩,
    (∑ i : Fin 7, compact[i.val].2) + left.2 + (∑ i : Fin 2, right[i.val].2) + 20)

theorem compression_source (v : Vector (Fin n) n) :
    compression v = CompressionDomains.prepare v := by
  have hr (i : Fin 2) : indexInterval n (rightStart n i) (rightLength n i) =
      compressionRightRaw n i := by
    unfold compressionRightRaw rightStart rightLength
    split <;> rfl
  simp only [compression, CompressionDomains.prepare, source, hr,
    compressionBlock, compressionLeftRaw]

theorem compression_work (v : Vector (Fin n) n) :
    (compression v).2 ≤ 500 * (n + 1) ^ 2 := by
  rw [compression_source]
  exact CompressionDomains.prepare_work v

end LowSpaceSubsetSum.IntervalDomainExecution

end OAI
