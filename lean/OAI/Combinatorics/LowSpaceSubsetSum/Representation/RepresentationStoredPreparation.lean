import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationLeafArrays
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredCoordinatePreparation

namespace OAI

/-! # Stored layout, leaves, and separator coordinates in one preparation -/

noncomputable section
namespace LowSpaceSubsetSum.RepresentationStoredPreparation

variable {n : ℕ}

structure Data (n : ℕ) where
  stored : RepresentationPrefixArrays.Data n
  leaves : RepresentationLeafArrays.Leaves n
  coordinates : StoredCoordinatePreparation.Rows n

def run (I : Instance n)
    (s : (canonicalRepresentationData I).zeroSetup.partitionHistoryCoupling.Seed) :
    Option (Data n) × ℕ :=
  let stored := RepresentationPrefixArrays.run (canonicalRepresentationData I) s
  match stored.1 with
  | none => (none, stored.2 + 1)
  | some data =>
    let leaves := RepresentationLeafArrays.run I data
    match leaves.1 with
    | none => (none, stored.2 + leaves.2 + 2)
    | some L =>
      let ordered := StoredOrderedMixers.run data.layout
      match ordered.1 with
      | none => (none, stored.2 + leaves.2 + ordered.2 + 3)
      | some domains =>
        let coordinates := StoredCoordinatePreparation.run domains data.partitions
        (coordinates.1.map (fun rows => ⟨data, L, rows⟩),
          stored.2 + leaves.2 + ordered.2 + coordinates.2 + 4)

theorem run_of_stages (I : Instance n)
    (s : (canonicalRepresentationData I).zeroSetup.partitionHistoryCoupling.Seed)
    (data : RepresentationPrefixArrays.Data n) (leaves : RepresentationLeafArrays.Leaves n)
    (domains : StoredOrderedMixers.Domains n) (rows : StoredCoordinatePreparation.Rows n)
    (hp : (RepresentationPrefixArrays.run (canonicalRepresentationData I) s).1 = some data)
    (hl : (RepresentationLeafArrays.run I data).1 = some leaves)
    (hd : (StoredOrderedMixers.run data.layout).1 = some domains)
    (hr : (StoredCoordinatePreparation.run domains data.partitions).1 = some rows) :
    (run I s).1 = some ⟨data, leaves, rows⟩ := by
  simp only [run, hp, hl, hd, hr, Option.map_some]

theorem prefix_result (I : Instance n)
    (s : (canonicalRepresentationData I).zeroSetup.partitionHistoryCoupling.Seed)
    (data : Data n) (h : (run I s).1 = some data) :
    (RepresentationPrefixArrays.run (canonicalRepresentationData I) s).1 = some data.stored := by
  simp only [run] at h
  split at h
  · contradiction
  next stored hp =>
    split at h
    · contradiction
    next leaves hl =>
      split at h
      · contradiction
      next domains hd =>
        obtain ⟨rows, _, he⟩ := Option.map_eq_some_iff.mp h
        cases he
        exact hp

theorem complete (I : Instance n)
    (s : (canonicalRepresentationData I).zeroSetup.partitionHistoryCoupling.Seed)
    (history : (canonicalRepresentationData I).zeroSetup.PartitionHistory)
    (h : (canonicalRepresentationData I).zeroSetup.partitionHistoryCoupling.bounded s = some history)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000) :
    ∃ data, (run I s).1 = some data ∧
      (RepresentationPrefixArrays.run (canonicalRepresentationData I) s).1 = some data.stored ∧
      (∀ (side : Fin 2) (i : Fin 4), data.leaves side i =
        (canonicalRepresentationData I).zeroSetup.rawLeaf history.1.1 history.1.2 history.2
          ((canonicalRepresentationData I).zeroSetup.allocatedBackground history.1.1 history.1.2 hn hlog)
          side i) ∧
      (∀ (a : Fin 4) (k : Fin (StoredTopCoordinates.width n)),
        (data.coordinates a)[k.val] =
          ((canonicalRepresentationData I).zeroSetup.topCoordinates history.1.1 history.2).index (a, k)) := by
  obtain ⟨stored, hp⟩ := RepresentationPrefixArrays.complete (canonicalRepresentationData I) s history h
  obtain ⟨h', leaves, hh', hl, hls⟩ := RepresentationLeafArrays.complete I s stored hp hn hlog
  have he : h' = history := Option.some.inj (hh'.symm.trans h)
  subst h'
  obtain ⟨h'', hh'', _, hv, _, hlabels, _⟩ :=
    RepresentationPrefixArrays.source (canonicalRepresentationData I) s stored hp
  have he : h'' = history := Option.some.inj (hh''.symm.trans h)
  subst h''
  obtain ⟨hL, _, _⟩ := RepresentationPrefixArrays.components (canonicalRepresentationData I) s stored hp
  obtain ⟨domains, hd, hds⟩ := StoredOrderedMixers.complete (canonicalRepresentationData I)
    s.1.1 stored.layout hL history.1.1.1 hv history.1.1.2
  obtain ⟨rows, hr, hrs⟩ := StoredCoordinatePreparation.complete (canonicalRepresentationData I).zeroSetup
    history.1.1 history.2 domains stored.partitions (hds 0) (hlabels 0)
  exact ⟨⟨stored, leaves, rows⟩, run_of_stages I s stored leaves domains rows hp hl hd hr, hp, hls, hrs⟩

theorem source (I : Instance n)
    (s : (canonicalRepresentationData I).zeroSetup.partitionHistoryCoupling.Seed)
    (data : Data n) (h : (run I s).1 = some data) (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000) :
    ∃ history : (canonicalRepresentationData I).zeroSetup.PartitionHistory,
      (canonicalRepresentationData I).zeroSetup.partitionHistoryCoupling.bounded s = some history ∧
      data.stored.layout.signs.semantic = history.1.1.2 ∧
      (∀ i : Fin n, data.stored.layout.permutation[i.val] = history.1.1.1 i) ∧
      (∀ j : Fin 3, data.stored.guesses[j.val] = (history.1.2 j).val) ∧
      (∀ j : Fin 4, data.stored.layout.parameters.widths[j.val] =
        (canonicalRepresentationData I).zeroSetup.samplerPrimeWidths history.1.1 j) ∧
      (∀ (side : Fin 2) (i : Fin 4), data.leaves side i =
        (canonicalRepresentationData I).zeroSetup.rawLeaf history.1.1 history.1.2 history.2
          ((canonicalRepresentationData I).zeroSetup.allocatedBackground history.1.1 history.1.2 hn hlog)
          side i) ∧
      (∀ (a : Fin 4) (k : Fin (StoredTopCoordinates.width n)),
        (data.coordinates a)[k.val] =
          ((canonicalRepresentationData I).zeroSetup.topCoordinates history.1.1 history.2).index (a, k)) := by
  obtain ⟨history, hh, hs, hv, hg, _, hw⟩ := RepresentationPrefixArrays.source
    (canonicalRepresentationData I) s data.stored (prefix_result I s data h)
  obtain ⟨other, ho, _, hl, hc⟩ := complete I s history hh hn hlog
  have he : other = data := Option.some.inj (ho.symm.trans h)
  subst other
  exact ⟨history, hh, hs, hv, hg, hw, hl, hc⟩

theorem domain_lengths (I : Instance n)
    (s : (canonicalRepresentationData I).zeroSetup.partitionHistoryCoupling.Seed)
    (data : RepresentationPrefixArrays.Data n)
    (h : (RepresentationPrefixArrays.run (canonicalRepresentationData I) s).1 = some data)
    (j : Fin 3) : data.layout.domains[j.val].length ≤ n := by
  obtain ⟨hL, _, _⟩ := RepresentationPrefixArrays.components (canonicalRepresentationData I) s data h
  obtain ⟨e, _, _, hd, _⟩ :=
    RepresentationLayoutPreparation.value (canonicalRepresentationData I) s.1.1 data.layout hL
  rw [hd j, Finset.length_sort, permuteSubset_card, (canonicalRepresentationData I).card j]
  unfold mixerSize
  omega

theorem work (I : Instance n)
    (s : (canonicalRepresentationData I).zeroSetup.partitionHistoryCoupling.Seed) :
    (run I s).2 ≤ (RepresentationPrefixArrays.run (canonicalRepresentationData I) s).2 +
      4000 * (n + 1) ^ 2 := by
  have hpos : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow 2 (n + 1) (by omega)
  simp only [run]
  split
  · dsimp only
    omega
  next data hp =>
    have hdomains := domain_lengths I s data hp
    have hleaves := RepresentationLeafArrays.work I data hdomains
    have horder := StoredOrderedMixers.work data.layout hdomains
    split
    · dsimp only
      omega
    next leaves hl =>
      split
      · dsimp only
        nlinarith only [hleaves, horder, hpos, Nat.zero_le n, Nat.zero_le (n ^ 2)]
      next domains hd =>
        have hc := StoredCoordinatePreparation.work domains data.partitions
        change _ + _ + _ + _ + 4 ≤ _
        nlinarith only [hleaves, horder, hc, hpos, Nat.zero_le n, Nat.zero_le (n ^ 2)]

end LowSpaceSubsetSum.RepresentationStoredPreparation

end

end OAI
