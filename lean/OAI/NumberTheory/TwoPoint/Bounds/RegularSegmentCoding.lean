import OAI.NumberTheory.TwoPoint.Bounds.QuotientPathNumbering
import OAI.NumberTheory.TwoPoint.Walks.ColumnChunkBudgets

namespace OAI

/-! Assemble all actual regular segments into one shared forest code. -/

namespace TwoPointCorrelations

open Finset

variable {K α ι : Type*} [Field K] [Fintype α] [DecidableEq ι]

/-- Enumerating nonempty segments does not require separate choices of line
names for each block. Their common quotient forest supplies one numbering. -/
theorem regular_segment_list_numbering {N : ℕ}
    (D : Submodule K (α → K)) (anchor : ι → (α → K) ⧸ D)
    (regularLabel : ι → α) (label : ℕ → α) (coefficient : ℕ → K)
    (hind : LinearIndependent K (fun j => D.mkQ (Pi.basisFun K α (regularLabel j))))
    (segments : List (List (ℕ × ι)))
    (hne : ∀ segment ∈ segments, segment ≠ [])
    (hstart : ∀ first rest, first :: rest ∈ segments → ∃ c : K,
      D.mkQ (formalDeparture label coefficient first.1) =
        anchor first.2 + c • D.mkQ (Pi.basisFun K α (regularLabel first.2)))
    (hdata : ∀ first rest, first :: rest ∈ segments →
      QuotientRunData D anchor regularLabel label coefficient first.1 first.2 rest)
    (hsize : 2 * (segments.map List.length).sum ≤ N) :
    ∃ (number : ι → ℕ) (code : ForestPathData.Code N segments.length),
      (∀ segment ∈ segments, ∀ p ∈ segment, number p.2 < N) ∧
      (∀ segment ∈ segments, ∀ p ∈ segment, ∀ other ∈ segments, ∀ q ∈ other,
        number p.2 = number q.2 → p.2 = q.2) ∧
      List.ofFn (fun i => evenEntries (decodeForestPaths code i)) =
        segments.map (fun segment => segment.map (fun p => number p.2)) := by
  let seg : Fin segments.length → List (ℕ × ι) := segments.get
  have hseg (i : Fin segments.length) : seg i ∈ segments := List.get_mem _ _
  let first := fun i => (seg i).head (hne _ (hseg i))
  let rest := fun i => (seg i).tail
  have hsplit (i : Fin segments.length) : first i :: rest i = seg i :=
    List.cons_head_tail (hne _ (hseg i))
  have hmem (i : Fin segments.length) : first i :: rest i ∈ segments := by
    rw [hsplit]; exact hseg i
  have hs : (∑ i, (2 * (rest i).length + 1)) ≤ N := by
    apply le_trans (sum_le_sum (fun i _ => ?_))
      ((show (∑ i, 2 * (seg i).length) = 2 * (segments.map List.length).sum by
        rw [← mul_sum]
        congr 1
        rw [← List.sum_ofFn]
        change (List.ofFn (List.length ∘ segments.get)).sum = _
        rw [← List.map_ofFn, List.ofFn_get]).le.trans hsize)
    have hl := congrArg List.length (hsplit i)
    simp only [List.length_cons] at hl
    omega
  obtain ⟨number, code, hbound, hinj, hdecode⟩ :=
    quotient_run_family_numbering D anchor regularLabel label coefficient hind
      (fun i => (first i).1) (fun i => (first i).2) rest
      (fun i => hstart _ _ (hmem i)) (fun i => hdata _ _ (hmem i)) hs
  have hlabels (i : Fin segments.length) :
      (first i).2 :: (rest i).map Prod.snd = (seg i).map Prod.snd := by
    rw [← hsplit i]; rfl
  refine ⟨number, code, ?_, ?_, ?_⟩
  · intro segment hm p hp
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hm
    apply hbound i p.2
    rw [hlabels]
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  · intro segment hm p hp other ho q hq heq
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hm
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp ho
    apply hinj i p.2 _ j q.2 _ heq
    · rw [hlabels]; exact List.mem_map.mpr ⟨p, hp, rfl⟩
    · rw [hlabels]; exact List.mem_map.mpr ⟨q, hq, rfl⟩
  · calc
      _ = List.ofFn (fun i => (seg i).map (fun p => number p.2)) := by
        congr 1
        funext i
        rw [hdecode, hlabels, List.map_map]
        rfl
      _ = _ := by
        change List.ofFn ((fun segment => segment.map (fun p => number p.2)) ∘ segments.get) = _
        rw [← List.map_ofFn, List.ofFn_get]

omit [Field K] [Fintype α] [DecidableEq ι] in
/-- Removing omitted runs cannot increase the total number of regular
vertices, even when a label is repeated in separate blocks. -/
theorem regular_pieces_total_length_le (pieces : List (List α ⊕ α)) :
    ((pieces.filterMap (Sum.elim some (fun _ => none))).map List.length).sum ≤
      (pieces.flatMap (Sum.elim id List.singleton)).length := by
  induction pieces with
  | nil => rfl
  | cons piece pieces ih =>
      cases piece with
      | inl segment => simpa using Nat.add_le_add_left ih segment.length
      | inr a =>
          simp only [List.filterMap_cons, Sum.elim_inr, List.flatMap_cons, List.length_append]
          simpa only [List.singleton, List.length_cons, List.length_nil, Nat.add_zero] using
            (ih.trans (Nat.le_add_left _ 1))

end TwoPointCorrelations

end OAI
