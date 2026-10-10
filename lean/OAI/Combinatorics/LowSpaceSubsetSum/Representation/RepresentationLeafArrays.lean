import OAI.Combinatorics.LowSpaceSubsetSum.Storage.StoredLeafPreparation
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationPrefixSource

namespace OAI

/-! # Preparing every leaf from the accepted stored prefix -/

namespace LowSpaceSubsetSum.RepresentationLeafArrays

variable {n : ℕ}

abbrev Leaves (n : ℕ) := Fin 2 → Fin 4 → RepresentationLeaf (Fin n)

def run (I : Instance n) (data : RepresentationPrefixArrays.Data n) : Option (Leaves n) × ℕ :=
  let ordered := StoredOrderedMixers.run data.layout
  match ordered.1 with
  | none => (none, ordered.2 + 1)
  | some domains =>
    let background := RepresentationBackgroundPreparation.run I data.layout.permutation data.guesses
    match background.1 with
    | none => (none, ordered.2 + background.2 + 2)
    | some rows =>
      let out := StoredLeafPreparation.run domains data.partitions rows data.guesses
      (some out.1, ordered.2 + background.2 + out.2 + 3)

theorem run_of_stages (I : Instance n) (data : RepresentationPrefixArrays.Data n)
    (domains : StoredOrderedMixers.Domains n) (background : Vector (List (Fin n)) 8)
    (hd : (StoredOrderedMixers.run data.layout).1 = some domains)
    (hb : (RepresentationBackgroundPreparation.run I data.layout.permutation data.guesses).1 = some background) :
    (run I data).1 = some (StoredLeafPreparation.run domains data.partitions background data.guesses).1 := by
  simp only [run, hd, hb]

theorem work (I : Instance n) (data : RepresentationPrefixArrays.Data n)
    (hl : ∀ j : Fin 3, data.layout.domains[j.val].length ≤ n) :
    (run I data).2 ≤ 3000 * (n + 1) ^ 2 := by
  have ho := StoredOrderedMixers.work data.layout hl
  have hb := RepresentationBackgroundPreparation.work I data.layout.permutation data.guesses
  simp only [run]
  split
  · dsimp only
    nlinarith only [ho, Nat.zero_le (n ^ 2)]
  next domains hd =>
    split
    · dsimp only
      nlinarith only [ho, hb, Nat.zero_le (n ^ 2)]
    next rows hr =>
      have hw := StoredLeafPreparation.work domains data.partitions rows data.guesses
        (RepresentationBackgroundPreparation.lengths I data.layout.permutation data.guesses rows hr)
      change _ + _ + _ + 3 ≤ _
      nlinarith only [ho, hb, hw, Nat.zero_le (n ^ 2)]

noncomputable section

theorem complete (I : Instance n)
    (s : (canonicalRepresentationData I).zeroSetup.partitionHistoryCoupling.Seed)
    (data : RepresentationPrefixArrays.Data n)
    (h : (RepresentationPrefixArrays.run (canonicalRepresentationData I) s).1 = some data)
    (hn : 10000 ≤ n)
    (hlog : Real.logb 2 ((mixerSize n : ℝ) + 1) + 1 ≤ (n : ℝ) / 1000) :
    ∃ history leaves,
      (canonicalRepresentationData I).zeroSetup.partitionHistoryCoupling.bounded s = some history ∧
      (run I data).1 = some leaves ∧
      ∀ (side : Fin 2) (i : Fin 4),
        leaves side i = (canonicalRepresentationData I).zeroSetup.rawLeaf
          history.1.1 history.1.2 history.2
          ((canonicalRepresentationData I).zeroSetup.allocatedBackground history.1.1 history.1.2 hn hlog)
          side i := by
  obtain ⟨history, hh, _, hv, hg, hl, _⟩ :=
    RepresentationPrefixArrays.source (canonicalRepresentationData I) s data h
  obtain ⟨hL, _, _⟩ := RepresentationPrefixArrays.components (canonicalRepresentationData I) s data h
  obtain ⟨domains, hd, hds⟩ := StoredOrderedMixers.complete (canonicalRepresentationData I)
    s.1.1 data.layout hL history.1.1.1 hv history.1.1.2
  obtain ⟨background, hb, hbs⟩ := RepresentationBackgroundPreparation.complete I
    data.layout.permutation history.1.1.1 hv history.1.1.2 data.guesses history.1.2 hg hn hlog
  refine ⟨history, (StoredLeafPreparation.run domains data.partitions background data.guesses).1,
    hh, run_of_stages I data domains background hd hb, ?_⟩
  intro side i
  exact StoredLeafPreparation.value (canonicalRepresentationData I).zeroSetup history.1.1
    history.1.2 history.2 _ domains data.partitions background data.guesses hds hl hbs hg side i

end
end LowSpaceSubsetSum.RepresentationLeafArrays

end OAI
