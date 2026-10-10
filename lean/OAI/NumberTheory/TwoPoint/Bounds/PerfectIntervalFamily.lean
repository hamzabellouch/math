import OAI.NumberTheory.TwoPoint.Bounds.PerfectBlockPositions

namespace OAI

/-! Choose numerical intervals for the constructed perfect blocks, preserving all budgets. -/

namespace TwoPointCorrelations

def intervalPositions (b : ℕ × ℕ) : List ℕ :=
  (List.range b.2).map (fun j => b.1 + j)

private theorem choose_interval_family (N : ℕ) (perfect : ℕ → Bool)
    (blocks : List (List ℕ))
    (hblocks : ∀ block ∈ blocks, ∃ start, start + block.length ≤ N ∧
      block = intervalPositions (start, block.length) ∧ ∀ i ∈ block, perfect i = true) :
    ∃ intervals : List (ℕ × ℕ), intervals.map intervalPositions = blocks ∧
      ∀ b ∈ intervals, b.1 + b.2 ≤ N ∧ ∀ i ∈ intervalPositions b, perfect i = true := by
  induction blocks with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons block blocks ih =>
      obtain ⟨start, hbound, heq, hp⟩ := hblocks block List.mem_cons_self
      obtain ⟨intervals, hi, hv⟩ := ih (fun b hb => hblocks b (List.mem_cons_of_mem _ hb))
      refine ⟨(start, block.length) :: intervals, ?_, ?_⟩
      · simpa only [List.map_cons, hi] using congrArg (fun tail => tail :: blocks) heq.symm
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ⟨hbound, by simpa only [← heq] using hp⟩
        · exact hv b hb

variable {α : Type*}

theorem perfectChunkLength_eq_sum (chunks : List (List α ⊕ α)) :
    perfectChunkLength chunks =
      ((chunks.filterMap (Sum.elim some (fun _ => none))).map List.length).sum := by
  induction chunks with
  | nil => rfl
  | cons chunk chunks ih =>
      cases chunk with
      | inl block =>
          simpa [perfectChunkLength, List.filterMap_cons, Sum.elim] using
            congrArg (fun n => block.length + n) ih
      | inr a =>
          simpa [perfectChunkLength, List.filterMap_cons, Sum.elim] using ih

/-- The actual short-block partition admits numerical interval parameters.
Their total length is at most the original length; every selected position
retains its original perfect flag. Empty terminal blocks cost zero. -/
theorem shortPerfectColumnChunks_interval_family (N s : ℕ) (perfect : ℕ → Bool) :
    ∃ intervals : List (ℕ × ℕ),
      intervals.map intervalPositions =
        ((shortPerfectColumnChunks s ((List.range N).map (fun i => (i, perfect i)))).filterMap
          (Sum.elim some (fun _ => none))) ∧
      intervals.length = perfectChunkCount
        (shortPerfectColumnChunks s ((List.range N).map (fun i => (i, perfect i)))) ∧
      (intervals.map Prod.snd).sum ≤ N ∧
      ∀ b ∈ intervals, b.1 + b.2 ≤ N ∧ ∀ i ∈ intervalPositions b, perfect i = true := by
  let chunks := shortPerfectColumnChunks s ((List.range N).map (fun i => (i, perfect i)))
  obtain ⟨intervals, he, hv⟩ := choose_interval_family N perfect
    (chunks.filterMap (Sum.elim some (fun _ => none))) (by
      intro block hb
      obtain ⟨piece, hp, heq⟩ := List.mem_filterMap.mp hb
      cases piece with
      | inl b =>
          cases heq
          exact shortPerfectColumnChunks_position_intervals N s perfect block hp
      | inr a => simp at heq)
  refine ⟨intervals, he, ?_, ?_, hv⟩
  · have h := congrArg List.length he
    simpa only [List.length_map, perfectChunkCount] using h
  · have hlen : (intervals.map Prod.snd).sum = perfectChunkLength chunks := by
      rw [perfectChunkLength_eq_sum, ← he, List.map_map]
      simp only [intervalPositions, List.length_map, List.length_range, Function.comp_def]
    rw [hlen]
    have h := perfectChunkLength_le_entries chunks
    rw [show columnChunkEntries chunks = (List.range N).map (fun i => (i, perfect i)) from
      shortPerfectColumnChunks_entries s _] at h
    simpa only [List.length_map, List.length_range] using h

end TwoPointCorrelations

end OAI
