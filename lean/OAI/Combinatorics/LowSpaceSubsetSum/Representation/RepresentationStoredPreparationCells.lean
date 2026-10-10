import OAI.Combinatorics.LowSpaceSubsetSum.Storage.PrefixPreparationCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.LeafArraysCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredCoordinateCells
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationStoredPreparation

namespace OAI

/-! # Full prepared prefix storage, including leaf and coordinate arrays

The accepted prefix remains live through leaf allocation and coordinate
sorting. The branch order and all returned work counters are preserved.
-/

noncomputable section
namespace LowSpaceSubsetSum.RepresentationStoredPreparationCells

variable {n : ℕ}

def extend (I : Instance n) (data : RepresentationPrefixArrays.Data n) :
    (Option (RepresentationStoredPreparation.Data n) × ℕ) × ℕ :=
  let leaves := LeafArraysCells.run I data
  match leaves.1.1 with
  | none => ((none, leaves.1.2+2), leaves.2+16*n+128)
  | some L =>
    let ordered := OrderedMixerCells.run data.layout
    match ordered.1.1 with
    | none => ((none, leaves.1.2+ordered.1.2+3), leaves.2+ordered.2+16*n+128)
    | some domains =>
      let coordinates := StoredCoordinateCells.run domains data.partitions
      ((coordinates.1.1.map (fun rows => ⟨data,L,rows⟩),
        leaves.1.2+ordered.1.2+coordinates.1.2+4),
        leaves.2+ordered.2+coordinates.2+16*n+128)

def run (I : Instance n)
    (s : (canonicalRepresentationData I).zeroSetup.partitionHistoryCoupling.Seed) :
    (Option (RepresentationStoredPreparation.Data n) × ℕ) × ℕ :=
  let stored := PrefixPreparationCells.run I s
  match stored.1.1 with
  | none => ((none, stored.1.2+1), stored.2+16*n+128)
  | some data =>
    let out := extend I data
    ((out.1.1, stored.1.2+out.1.2), stored.2+out.2+16*n+128)

theorem value (I : Instance n)
    (s : (canonicalRepresentationData I).zeroSetup.partitionHistoryCoupling.Seed) :
    (run I s).1 = RepresentationStoredPreparation.run I s := by
  have hp₁ := congrArg Prod.fst (PrefixPreparationCells.value I s)
  have hp₂ := congrArg Prod.snd (PrefixPreparationCells.value I s)
  simp only [run, hp₁, hp₂, RepresentationStoredPreparation.run]
  split
  · simp_all only
  next data h =>
    have hl₁ := congrArg Prod.fst (LeafArraysCells.value I data)
    have hl₂ := congrArg Prod.snd (LeafArraysCells.value I data)
    have ho₁ := congrArg Prod.fst (OrderedMixerCells.value data.layout)
    have ho₂ := congrArg Prod.snd (OrderedMixerCells.value data.layout)
    simp only [extend, hl₁, hl₂, ho₁, ho₂]
    split
    · simp_all only [Nat.add_assoc]
    · split
      · simp_all only [Nat.add_assoc]
      next domains h =>
        have hc₁ := congrArg Prod.fst (StoredCoordinateCells.value domains data.partitions)
        have hc₂ := congrArg Prod.snd (StoredCoordinateCells.value domains data.partitions)
        simp_all only [Nat.add_assoc]

theorem extend_cells (I : Instance n) (data : RepresentationPrefixArrays.Data n)
    (hl : ∀ j : Fin 3, data.layout.domains[j.val].length ≤ n) :
    (extend I data).2 ≤ 32768*(n+1)^2 := by
  have hL := LeafArraysCells.cells I data hl
  have hO := OrderedMixerCells.cells data.layout hl
  unfold extend
  dsimp only
  split
  · nlinarith only [hL, Nat.zero_le (n^2)]
  next L h =>
    split
    · nlinarith only [hL, hO, Nat.zero_le (n^2)]
    next domains h =>
      have hC := StoredCoordinateCells.cells domains data.partitions
      nlinarith only [hL, hO, hC, Nat.zero_le (n^2)]

private theorem scalar_bound (n u C P Q : ℕ) (hu : n+2 ≤ u) (hu0 : 10000 ≤ u)
    (hP : P ≤ u^11*(C+1)) (hQ : Q ≤ 32768*(n+1)^2) :
    P+Q+16*n+128 ≤ u^12*(C+1) := by
  have hq := Nat.pow_le_pow_left (show n+1 ≤ u by omega) 2
  have hpoly : 32768*(n+1)^2+16*n+128 ≤ u^4 := by
    have hu2 : 1 ≤ u^2 := Nat.one_le_pow _ _ (by omega)
    have hcoef : 33000 ≤ u^2 := by nlinarith only [hu0]
    have hm := Nat.mul_le_mul_right (u^2) hcoef
    rw [← pow_add] at hm
    change 33000*u^2 ≤ u^4 at hm
    nlinarith only [hq, hu, hu0, hu2, hm]
  have h411 : u^4 ≤ u^11 := pow_le_pow_right' (by omega) (by decide)
  have hsmall := hpoly.trans (h411.trans (Nat.le_mul_of_pos_right _ (by omega : 0 < C+1)))
  have hf : 2*u^11 ≤ u^12 := by
    calc
      _ ≤ u*u^11 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  have hm := Nat.mul_le_mul_right (C+1) hf
  simp only [Nat.mul_assoc] at hm
  omega

theorem cells (I : Instance n) (hn : 10000 ≤ n)
    (s : (canonicalRepresentationData I).zeroSetup.partitionHistoryCoupling.Seed) :
    (run I s).2 ≤ inputScale I^12*(compressionDictionaryCapacity n+1) := by
  have hp := PrefixPreparationCells.cells I hn s
  unfold run
  dsimp only
  split
  · have hs := scalar_bound n (inputScale I) (compressionDictionaryCapacity n)
      (PrefixPreparationCells.run I s).2 0 (by unfold inputScale; omega)
      (by unfold inputScale; omega) hp (Nat.zero_le _)
    omega
  next data h =>
    have hs : (RepresentationPrefixArrays.run (canonicalRepresentationData I) s).1 = some data := by
      rw [← PrefixPreparationCells.value I s]
      exact h
    have he := extend_cells I data (RepresentationStoredPreparation.domain_lengths I s data hs)
    exact scalar_bound n (inputScale I) (compressionDictionaryCapacity n)
      (PrefixPreparationCells.run I s).2 (extend I data).2
      (by unfold inputScale; omega) (by unfold inputScale; omega) hp he

end LowSpaceSubsetSum.RepresentationStoredPreparationCells

end

end OAI
