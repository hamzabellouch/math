import OAI.NumberTheory.TwoPoint.Bounds.RegularSegmentCoding
import OAI.NumberTheory.TwoPoint.Bounds.RunCoverage

namespace OAI

/-! The actual indexed regular segments of a finite family of perfect blocks. -/

namespace TwoPointCorrelations

open Finset

private theorem decoded_forest_transport {N S T : ℕ} (h : S = T)
    (code : ForestPathData.Code N S) :
    List.ofFn (fun i => evenEntries (decodeForestPaths (h ▸ code) i)) =
      List.ofFn (fun i => evenEntries (decodeForestPaths code i)) := by
  cases h
  rfl

variable {α : Type*} [DecidableEq α]

def indexedRegularSegments (label : ℕ → α) (omitted : α → Bool)
    (blocks : List (ℕ × ℕ)) : List (List (ℕ × α)) :=
  blocks.flatMap (fun b =>
    (partitionColumnRuns (fun p => omitted p.2) (indexedBlockRuns label b.1 b.2)).filterMap
      (Sum.elim some (fun _ => none)))

theorem mem_indexedRegularSegments (label : ℕ → α) (omitted : α → Bool)
    (blocks : List (ℕ × ℕ)) (segment : List (ℕ × α)) :
    segment ∈ indexedRegularSegments label omitted blocks ↔
      ∃ b ∈ blocks, Sum.inl segment ∈
        partitionColumnRuns (fun p => omitted p.2) (indexedBlockRuns label b.1 b.2) := by
  simp only [indexedRegularSegments, List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨b, hb, piece, hp, he⟩
    cases piece with
    | inl s => cases he; exact ⟨b, hb, hp⟩
    | inr z => simp at he
  · rintro ⟨b, hb, hs⟩
    exact ⟨b, hb, .inl segment, hs, rfl⟩

theorem indexedRegularSegments_nonempty (label : ℕ → α) (omitted : α → Bool)
    (blocks : List (ℕ × ℕ)) (segment : List (ℕ × α))
    (hs : segment ∈ indexedRegularSegments label omitted blocks) : segment ≠ [] := by
  obtain ⟨b, _, hb⟩ := (mem_indexedRegularSegments label omitted blocks segment).mp hs
  exact (partitionColumnRuns_regular_entries _ _ _ hb).1

theorem indexedBlockRuns_length_le (label : ℕ → α) (start len : ℕ) :
    (indexedBlockRuns label start len).length ≤ len := by
  have h := columnRunHeads_length_le ((blockLabelList label start len).map some) none
  rw [← indexedBlockRuns_labels] at h
  simpa only [List.length_map, blockLabelList, List.length_range] using h

/-- The total number of retained regular run starts is bounded by the
number of original positions, with no factor for the number of labels. -/
theorem indexedRegularSegments_total_length (label : ℕ → α) (omitted : α → Bool)
    (blocks : List (ℕ × ℕ)) :
    ((indexedRegularSegments label omitted blocks).map List.length).sum ≤
      (blocks.map Prod.snd).sum := by
  induction blocks with
  | nil => rfl
  | cons b blocks ih =>
      have hb := regular_pieces_total_length_le
        (partitionColumnRuns (fun p => omitted p.2) (indexedBlockRuns label b.1 b.2))
      rw [partitionColumnRuns_flatten] at hb
      have hb' := hb.trans (indexedBlockRuns_length_le label b.1 b.2)
      simpa only [indexedRegularSegments, List.flatMap_cons, List.map_append,
        List.sum_append, List.map_cons, List.sum_cons] using Nat.add_le_add hb' ih

/-- Every regular label seen in a block survives both compression and the
omitted-label cut, so its forest line is included in the shared numbering. -/
theorem indexedRegularSegments_cover (label : ℕ → α) (omitted : α → Bool)
    (blocks : List (ℕ × ℕ)) (b : ℕ × ℕ) (hb : b ∈ blocks) (z : α)
    (hz : z ∈ blockLabelList label b.1 b.2) (hregular : omitted z = false) :
    ∃ segment ∈ indexedRegularSegments label omitted blocks, ∃ p ∈ segment, p.2 = z := by
  have hr := mem_columnRunHeads _ z hz
  rw [← indexedBlockRuns_labels] at hr
  obtain ⟨p, hp, he⟩ := List.mem_map.mp hr
  obtain ⟨segment, hs, hps⟩ := partitionColumnRuns_regular_cover
    (fun p : ℕ × α => omitted p.2) (indexedBlockRuns label b.1 b.2) p hp (by rw [he]; exact hregular)
  exact ⟨segment, (mem_indexedRegularSegments label omitted blocks segment).mpr ⟨b, hb, hs⟩,
    p, hps, he⟩

variable {K ι : Type*} [Field K] [Fintype α] [DecidableEq ι]

/-- Number the regular paths actually produced by the given blocks.
The hypotheses are line incidence and nonvanishing physical intervals;
all path, compression, coverage and size data are constructed here. -/
theorem indexed_block_family_numbering {N : ℕ}
    (D : Submodule K (α → K)) (anchor : ι → (α → K) ⧸ D)
    (regularLabel : ι → α) (rename : α → ι)
    (label : ℕ → α) (coefficient : ℕ → K) (omitted : α → Bool)
    (blocks : List (ℕ × ℕ))
    (hind : LinearIndependent K (fun j => D.mkQ (Pi.basisFun K α (regularLabel j))))
    (hname : ∀ z, omitted z = false → regularLabel (rename z) = z)
    (hline : ∀ b ∈ blocks, ∀ t ∈ Ico b.1 (b.1 + b.2), omitted (label t) = false →
      ∃ c : K, D.mkQ (formalDeparture label coefficient t) = anchor (rename (label t)) +
        c • D.mkQ (Pi.basisFun K α (regularLabel (rename (label t)))))
    (hnonzero : ∀ b ∈ blocks, ∀ a e z, b.1 ≤ a → a < e → e ≤ b.1 + b.2 →
      (∀ t ∈ Ico a e, label t = z) → (∑ t ∈ Ico a e, coefficient t) ≠ 0)
    (hsize : 2 * (blocks.map Prod.snd).sum ≤ N) :
    ∃ (number : ι → ℕ)
      (code : ForestPathData.Code N (indexedRegularSegments label omitted blocks).length),
      (∀ segment ∈ indexedRegularSegments label omitted blocks,
        ∀ p ∈ segment, number (rename p.2) < N) ∧
      (∀ segment ∈ indexedRegularSegments label omitted blocks, ∀ p ∈ segment,
        ∀ other ∈ indexedRegularSegments label omitted blocks, ∀ q ∈ other,
        number (rename p.2) = number (rename q.2) → p.2 = q.2) ∧
      List.ofFn (fun i => evenEntries (decodeForestPaths code i)) =
        (indexedRegularSegments label omitted blocks).map
          (fun segment => segment.map (fun p => number (rename p.2))) := by
  let segments := indexedRegularSegments label omitted blocks
  let relabel := fun p : ℕ × α => (p.1, rename p.2)
  let renamed := segments.map (List.map relabel)
  have hreg : ∀ segment ∈ segments, ∀ p ∈ segment, omitted p.2 = false := by
    intro segment hs p hp
    obtain ⟨b, _, hb⟩ := (mem_indexedRegularSegments label omitted blocks segment).mp hs
    exact (partitionColumnRuns_regular_entries _ _ _ hb).2 p hp
  have horigin : ∀ first rest, first :: rest ∈ renamed →
      ∃ p ps b, p :: ps ∈ segments ∧ b ∈ blocks ∧
        Sum.inl (p :: ps) ∈ partitionColumnRuns (fun p => omitted p.2)
          (indexedBlockRuns label b.1 b.2) ∧ first = relabel p ∧ rest = ps.map relabel := by
    intro first rest hs
    obtain ⟨segment, hsegment, he⟩ := List.mem_map.mp hs
    cases segment with
    | nil => simp at he
    | cons p ps =>
        obtain ⟨b, hb, hp⟩ := (mem_indexedRegularSegments label omitted blocks _).mp hsegment
        simp only [List.map_cons, List.cons.injEq] at he
        exact ⟨p, ps, b, hsegment, hb, hp, he.1.symm, he.2.symm⟩
  have hne : ∀ segment ∈ renamed, segment ≠ [] := by
    intro segment hs
    obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hs
    intro he
    exact indexedRegularSegments_nonempty label omitted blocks original ho (List.eq_nil_of_map_eq_nil he)
  have hstart : ∀ first rest, first :: rest ∈ renamed → ∃ c : K,
      D.mkQ (formalDeparture label coefficient first.1) =
        anchor first.2 + c • D.mkQ (Pi.basisFun K α (regularLabel first.2)) := by
    intro first rest hs
    obtain ⟨p, ps, b, _, hb, hp, rfl, _⟩ := horigin first rest hs
    have hm := (partitionColumnRuns_regular_infix _ _ _ hp).subset (List.mem_cons_self)
    obtain ⟨hl, hu, he⟩ := indexedBlockRuns_mem label b.1 b.2 p hm
    simpa only [relabel, he] using hline b hb p.1 (mem_Ico.mpr ⟨hl, hu⟩)
      (by rw [he]; exact (partitionColumnRuns_regular_entries _ _ _ hp).2 p List.mem_cons_self)
  have hdata : ∀ first rest, first :: rest ∈ renamed →
      QuotientRunData D anchor regularLabel label coefficient first.1 first.2 rest := by
    intro first rest hs
    obtain ⟨p, ps, b, _, hb, hp, rfl, rfl⟩ := horigin first rest hs
    exact indexed_regular_piece_quotient_data D anchor regularLabel rename label coefficient
      b.1 b.2 omitted p ps hp hname (hline b hb) (hnonzero b hb)
  have hbudget : 2 * (renamed.map List.length).sum ≤ N := by
    have h := Nat.mul_le_mul_left 2 (indexedRegularSegments_total_length label omitted blocks)
    simpa only [renamed, List.map_map, List.length_map, Function.comp_def] using h.trans hsize
  obtain ⟨number, code, hbound, hinj, hdecode⟩ := regular_segment_list_numbering D anchor
    regularLabel label coefficient hind renamed hne hstart hdata hbudget
  have hrenamedLength : renamed.length = segments.length := List.length_map (List.map relabel)
  let code' : ForestPathData.Code N segments.length := hrenamedLength ▸ code
  have hcode : List.ofFn (fun i => evenEntries (decodeForestPaths code' i)) =
      segments.map (fun segment => segment.map (fun p => number (rename p.2))) := by
    change List.ofFn (fun i => evenEntries (decodeForestPaths (hrenamedLength ▸ code) i)) = _
    rw [decoded_forest_transport]
    simpa only [renamed, List.map_map, relabel, Function.comp_def] using hdecode
  refine ⟨number, code', ?_, ?_, hcode⟩
  · intro segment hs p hp
    exact hbound (segment.map relabel) (List.mem_map.mpr ⟨segment, hs, rfl⟩)
      (relabel p) (List.mem_map.mpr ⟨p, hp, rfl⟩)
  · intro segment hs p hp other ho q hq he
    have hr := hinj (segment.map relabel) (List.mem_map.mpr ⟨segment, hs, rfl⟩)
      (relabel p) (List.mem_map.mpr ⟨p, hp, rfl⟩)
      (other.map relabel) (List.mem_map.mpr ⟨other, ho, rfl⟩)
      (relabel q) (List.mem_map.mpr ⟨q, hq, rfl⟩) he
    exact (hname p.2 (hreg segment hs p hp)).symm.trans
      ((congrArg regularLabel hr).trans (hname q.2 (hreg other ho q hq)))

end TwoPointCorrelations

end OAI
