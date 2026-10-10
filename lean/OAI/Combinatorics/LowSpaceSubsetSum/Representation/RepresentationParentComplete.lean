import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationEntrySoundness
import OAI.Combinatorics.LowSpaceSubsetSum.Streams.DictionaryCompleted

namespace OAI

/-! # Complete bounded parent arrays and preservation of exact entry keys -/

namespace LowSpaceSubsetSum.RepresentationParentData

variable {n : ℕ} (D : RepresentationParentData n)

/-- Mathematical list of valid entries emitted by this task. The executable
collector keeps only the bounded deduplicated array. -/
def rawEntries : List (Entry (Fin n)) :=
  RecordedDictionary.matchingRecords (D.key 0) (D.key 1) D.emit
    ((D.pair 0).output (D.pair 0).start) ((D.pair 1).output (D.pair 1).start)

def RawEligible (x : Parent (n := n)) : Prop :=
  x.1 ∈ (D.pair 0).output (D.pair 0).start ∧
    x.2 ∈ (D.pair 1).output (D.pair 1).start ∧
      D.key 0 x.1 = D.key 1 x.2 ∧ RepresentationUniverse.Valid x

theorem key_match_iff (x : Parent (n := n)) :
    D.key 0 x.1 = D.key 1 x.2 ↔
      RepresentationUniverse.parentWeight D.weights x % D.modulus =
        D.parentResidue % D.modulus := by
  change (RepresentationLeaf.occurrenceWeight D.weights x.1.1 +
      RepresentationLeaf.occurrenceWeight D.weights x.1.2) % D.modulus =
    (D.parentResidue - RepresentationLeaf.occurrenceWeight D.weights x.2.1 -
      RepresentationLeaf.occurrenceWeight D.weights x.2.2) % D.modulus ↔ _
  rw [← sub_add_eq_sub_sub]
  change Int.ModEq D.modulus (RepresentationUniverse.childWeight D.weights x.1)
    (D.parentResidue - RepresentationUniverse.childWeight D.weights x.2) ↔
      Int.ModEq D.modulus (RepresentationUniverse.childWeight D.weights x.1 +
        RepresentationUniverse.childWeight D.weights x.2) D.parentResidue
  constructor
  · intro h
    simpa only [sub_add_cancel] using h.add_right (RepresentationUniverse.childWeight D.weights x.2)
  · intro h
    simpa only [add_sub_cancel_right] using h.sub_right (RepresentationUniverse.childWeight D.weights x.2)

theorem rawEligible_parent_mod (x : Parent (n := n)) (hx : D.RawEligible x) :
    RepresentationUniverse.parentWeight D.weights x % D.modulus =
      D.parentResidue % D.modulus := (D.key_match_iff x).mp hx.2.2.1

/-- The two low child filters and one full parent filter place a designated
raw tuple in the actual streams. Prefix tests are on its individual leaves. -/
theorem rawEligible_of_filters (x : Parent (n := n))
    (hx : x ∈ RepresentationUniverse.parents D.leaves) (hv : RepresentationUniverse.Valid x)
    (h0 : D.maskRestriction.Compatible (D.leaves 0).top x.1.1.1.1)
    (h1 : D.maskRestriction.Compatible (D.leaves 1).top x.1.2.1.1)
    (h2 : D.maskRestriction.Compatible (D.leaves 2).top x.2.1.1.1)
    (h3 : D.maskRestriction.Compatible (D.leaves 3).top x.2.2.1.1)
    (hc0 : RepresentationUniverse.childWeight D.weights x.1 % D.lowModulus =
      D.childResidues 0 % D.lowModulus)
    (hc1 : RepresentationUniverse.childWeight D.weights x.2 % D.lowModulus =
      D.childResidues 1 % D.lowModulus)
    (hp : RepresentationUniverse.parentWeight D.weights x % D.modulus =
      D.parentResidue % D.modulus) : D.RawEligible x := by
  obtain ⟨hx0, hx1, hx2, hx3⟩ := (RepresentationUniverse.mem_parents D.leaves x).mp hx
  refine ⟨((D.pair 0).output_mem x.1).mpr ?_, ((D.pair 1).output_mem x.2).mpr ?_, ?_, hv⟩
  · exact ⟨⟨hx0, (D.maskRestriction.accept_eq_true _ _).mpr h0⟩,
      ⟨hx1, (D.maskRestriction.accept_eq_true _ _).mpr h1⟩, hc0⟩
  · exact ⟨⟨hx2, (D.maskRestriction.accept_eq_true _ _).mpr h2⟩,
      ⟨hx3, (D.maskRestriction.accept_eq_true _ _).mpr h3⟩, hc1⟩
  · exact (D.key_match_iff x).mpr hp

theorem rawEntries_mem (e : Entry (Fin n)) :
    e ∈ D.rawEntries ↔ ∃ x, D.RawEligible x ∧ RepresentationUniverse.entry D.weights x = e := by
  rw [rawEntries, RecordedDictionary.mem_matchingRecords]
  constructor
  · rintro ⟨x, hx, y, hy, hk, he⟩
    obtain ⟨hv, he⟩ := (D.emit_some_iff x y e).mp he
    exact ⟨(x, y), ⟨hx, hy, hk, hv⟩, he⟩
  · rintro ⟨⟨x, y⟩, ⟨hx, hy, hk, hv⟩, he⟩
    exact ⟨x, hx, y, hy, hk, (D.emit_some_iff x y e).mpr ⟨hv, he⟩⟩

theorem rawEntries_parent_mod (e : Entry (Fin n)) (he : e ∈ D.rawEntries) :
    e.value % D.modulus = D.parentResidue % D.modulus := by
  obtain ⟨x, hx, rfl⟩ := (D.rawEntries_mem e).mp he
  exact D.rawEligible_parent_mod x hx

theorem collect_eq_records (B : ℕ) :
    (D.collect B).state.user = D.rawEntries.foldl
      (fun r z => RecordedDictionary.feed D.capacity (WeightEncoding.entryKey D.input) z r)
      RecordedDictionary.empty := by
  have h0 := (D.pair 0).output_length_le
  have h1 := (D.pair 1).output_length_le
  exact RecordedDictionary.join_eq_records D.capacity (WeightEncoding.entryKey D.input)
    (D.pair 0).read (D.key 0) (D.pair 1).read (D.key 1) D.emit
    (D.pair 0).output (D.pair 0).read_law (D.pair 1).output (D.pair 1).read_law
    B _ _ _ (D.pair 0).start (D.pair 1).start RecordedDictionary.empty
    (D.pair 0).output_sorted (D.pair 1).output_sorted h0 h1 (by omega)

theorem entries_raw (B : ℕ) (e : Entry (Fin n)) (he : e ∈ (D.entries B).toList) :
    e ∈ D.rawEntries := by
  have he' : e ∈ (D.collect B).state.user.records.toList := he
  rw [D.collect_eq_records B] at he'
  exact RecordedDictionary.fold_provenance D.capacity (WeightEncoding.entryKey D.input)
    D.rawEntries RecordedDictionary.empty (· ∈ D.rawEntries)
    (by simp [RecordedDictionary.empty]) (fun _ h => h) e he'

/-- Equal keys can arise from many repeated raw representations. The bound
is on the containing distinct-entry universe, not the number of reports. -/
theorem collect_fits (B : ℕ) (U : Finset (Entry (Fin n)))
    (hcap : U.card ≤ D.capacity) (hU : ∀ e ∈ D.rawEntries, e ∈ U) :
    (D.collect B).state.user.keys.overflow = false ∧ ∀ q,
      (∃ e ∈ (D.entries B).toList, WeightEncoding.entryKey D.input e = q) ↔
        ∃ e ∈ D.rawEntries, WeightEncoding.entryKey D.input e = q := by
  classical
  have hf := RecordedDictionary.fold_fits (width := WeightEncoding.entryWidth D.input)
    (C := D.capacity) (WeightEncoding.entryKey D.input) D.rawEntries
    (U.image (WeightEncoding.entryKey D.input)) (by
      intro q hq
      obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hq
      exact WeightEncoding.entryKey_length D.input e)
    ((Finset.card_image_le).trans hcap) (by
      intro e he
      exact Finset.mem_image.mpr ⟨e, hU e he, rfl⟩)
  dsimp only [entries]
  rw [D.collect_eq_records B]
  exact hf

/-- Fixed-width keys lose no exact weight/mask entry on the actual bounded
weight universe. Deduplication can change the witness but not the entry. -/
theorem entries_mem_iff (B : ℕ) (U : Finset (Entry (Fin n)))
    (hcap : U.card ≤ D.capacity) (hU : ∀ e ∈ D.rawEntries, e ∈ U)
    (hbounded : ∀ e ∈ U, WeightEncoding.BoundedWeight D.input e.value)
    (e : Entry (Fin n)) : e ∈ (D.entries B).toList ↔ e ∈ D.rawEntries := by
  constructor
  · exact D.entries_raw B e
  · intro he
    obtain ⟨f, hf, hk⟩ := ((D.collect_fits B U hcap hU).2
      (WeightEncoding.entryKey D.input e)).mpr ⟨e, he, rfl⟩
    have hfe : f = e := WeightEncoding.entryKey_injective D.input
      (hbounded f (hU f (D.entries_raw B f hf))) (hbounded e (hU e he)) hk
    exact hfe ▸ hf

/-- A completed task retains every emitted exact entry, whether or not an
ambient capacity bound was supplied in advance. -/
theorem entries_mem_iff_of_complete (B : ℕ)
    (hc : (D.collect B).state.user.keys.overflow = false)
    (hbounded : ∀ e ∈ D.rawEntries, WeightEncoding.BoundedWeight D.input e.value)
    (e : Entry (Fin n)) : e ∈ (D.entries B).toList ↔ e ∈ D.rawEntries := by
  have hc' := hc
  rw [D.collect_eq_records B] at hc'
  have hk := RecordedDictionary.fold_complete (width := WeightEncoding.entryWidth D.input)
    (WeightEncoding.entryKey D.input) D.rawEntries
    (fun e _ => WeightEncoding.entryKey_length D.input e) hc'
  constructor
  · exact D.entries_raw B e
  · intro he
    obtain ⟨f, hf, hkey⟩ := (hk (WeightEncoding.entryKey D.input e)).mpr ⟨e, he, rfl⟩
    have hf' : f ∈ (D.entries B).toList := by
      change f ∈ (D.collect B).state.user.records.toList
      rw [D.collect_eq_records B]
      exact hf
    have hfe : f = e := WeightEncoding.entryKey_injective D.input
      (hbounded f (D.entries_raw B f hf')) (hbounded e he) hkey
    exact hfe ▸ hf'

theorem rawEntries_represents
    (htl : Disjoint (RepresentationUniverse.topDomain D.leaves)
      (RepresentationUniverse.mixerDomain D.leaves))
    (htb : Disjoint (RepresentationUniverse.topDomain D.leaves)
      (RepresentationUniverse.backgroundDomain D.leaves))
    (hlb : Disjoint (RepresentationUniverse.mixerDomain D.leaves)
      (RepresentationUniverse.backgroundDomain D.leaves))
    (e : Entry (Fin n)) (he : e ∈ D.rawEntries) :
    Represents D.weights (RepresentationUniverse.parentDomain D.leaves)
      (RepresentationUniverse.topDomain D.leaves) e := by
  obtain ⟨x, ⟨hx, hy, _, hv⟩, rfl⟩ := (D.rawEntries_mem e).mp he
  exact RepresentationUniverse.entry_represents D.weights D.leaves htl htb hlb
    (D.streams_parent x.1 x.2 hx hy) hv

end LowSpaceSubsetSum.RepresentationParentData

end OAI
