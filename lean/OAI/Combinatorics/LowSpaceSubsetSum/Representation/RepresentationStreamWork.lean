import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationParentComplete

namespace OAI

/-! # Occurrence counts and stopped query ledgers for concrete parent streams

The list and finite-set views below are proof objects. Runtime still uses the
shared leaf arrays and constant-state tournament readers.
-/

namespace LowSpaceSubsetSum

open scoped BigOperators

namespace FilteredStream

variable {α β : Type*}

private theorem product_filter_bag (xs : List α) (ys : List β) (p : α × β → Bool) :
    ((xs ×ˢ ys).filter p : Multiset (α × β)) =
      (xs.map (fun x => ((ys.filter (fun y => p (x, y))).map (fun y => (x, y)) :
        Multiset (α × β)))).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.product_cons, List.filter_append, List.filter_map,
      ← Multiset.coe_add, List.map_cons, List.sum_cons, Function.comp_def, ih]

/-- The actual output is a permutation of the filtered indexed Cartesian
product, so equal numerical weights do not collapse occurrence identities. -/
theorem sorted_output_perm (left : Array α) (right : Array β)
    (wl : α → ℤ) (wr : β → ℤ) (p P c : ℤ) (hP : 0 < P) (mode : Mode) :
    (MergedReader.output (key wl wr P mode) (read (ResidueSort.sort right wr p P))
      (view (ResidueSort.sort right wr p P)) (sortedStart left right wl wr p P c hP mode)).Perm
      ((left.toList ×ˢ right.toList).filter
        (fun z => decide ((wl z.1 + wr z.2) % p = c % p))) := by
  apply Multiset.coe_eq_coe.mp
  rw [sorted_output_bag, product_filter_bag]
  have hl : List.ofFn (fun i : Fin left.size => left[i.val]) = left.toList := by
    simpa only [Array.toList_ofFn] using
      congrArg Array.toList (Array.ofFn_getElem (xs := left))
  rw [← List.sum_ofFn, ← hl, List.map_ofFn]
  rfl

end FilteredStream

namespace RepresentationPairData

variable {n : ℕ} (D : RepresentationPairData n)

theorem output_perm : (D.output D.start).Perm
    ((D.leftArray.toList ×ˢ D.rightArray.toList).filter
      (fun z => decide (RepresentationUniverse.childWeight D.weights z % D.lowModulus =
        D.residue % D.lowModulus))) := by
  convert FilteredStream.sorted_output_perm D.leftArray D.rightArray D.wl D.wl
      D.lowModulus D.modulus D.residue D.positive D.mode using 1 <;> rfl

theorem output_nodup : (D.output D.start).Nodup := by
  apply D.output_perm.nodup_iff.mpr
  apply List.Nodup.filter
  exact (D.left.enumerate_nodup.filter _).product (D.right.enumerate_nodup.filter _)

def outputUniverse : Finset (RepresentationUniverse.ChildOccurrence (Fin n)) :=
  (D.left.occurrences ×ˢ D.right.occurrences).filter (fun z =>
    D.acceptLeft z.1 && D.acceptRight z.2 &&
      decide (RepresentationUniverse.childWeight D.weights z % D.lowModulus =
        D.residue % D.lowModulus))

theorem output_toFinset : (D.output D.start).toFinset = D.outputUniverse := by
  ext x
  simp only [List.mem_toFinset, output_mem, outputUniverse, Finset.mem_filter,
    Finset.mem_product, Bool.and_eq_true, decide_eq_true_eq]
  tauto

theorem output_length_eq_card : (D.output D.start).length = D.outputUniverse.card := by
  rw [← D.output_toFinset, List.toFinset_card_of_nodup D.output_nodup]

end RepresentationPairData

namespace MatchPotential

variable {α β : Type*}

/-- Cartesian occurrence identity for the actual join potential. -/
theorem count_eq_filter_product_length (key₁ : α → ℤ) (key₂ : β → ℤ)
    (xs : List α) (ys : List β) :
    count key₁ key₂ xs ys =
      ((xs ×ˢ ys).filter (fun z => decide (key₁ z.1 = key₂ z.2))).length := by
  induction xs with
  | nil => simp [count]
  | cons x xs ih =>
    simp only [count, List.product_cons, List.filter_append, List.filter_map,
      List.length_append, List.length_map, Function.comp_def, ih]

end MatchPotential

namespace RepresentationParentData

variable {n : ℕ} (D : RepresentationParentData n)

/-- Raw matching occurrences include those rejected by the validity callback. -/
def matchingUniverse : Finset (Parent (n := n)) :=
  ((D.pair 0).outputUniverse ×ˢ (D.pair 1).outputUniverse).filter
    (fun z => D.key 0 z.1 = D.key 1 z.2)

theorem matching_potential_eq_card :
    MatchPotential.count (D.key 0) (D.key 1)
      ((D.pair 0).output (D.pair 0).start) ((D.pair 1).output (D.pair 1).start) =
        D.matchingUniverse.card := by
  classical
  let xs := (D.pair 0).output (D.pair 0).start
  let ys := (D.pair 1).output (D.pair 1).start
  let matched := (xs ×ˢ ys).filter (fun z => decide (D.key 0 z.1 = D.key 1 z.2))
  have hn : matched.Nodup := ((D.pair 0).output_nodup.product
    (D.pair 1).output_nodup).filter _
  have he : matched.toFinset = D.matchingUniverse := by
    ext z
    rcases z with ⟨x, y⟩
    simp only [matched, xs, ys, List.mem_toFinset, List.mem_filter, List.mem_product,
      matchingUniverse, Finset.mem_filter, Finset.mem_product, decide_eq_true_eq,
      ← (D.pair 0).output_toFinset, ← (D.pair 1).output_toFinset]
  rw [MatchPotential.count_eq_filter_product_length]
  change matched.length = _
  rw [← List.toFinset_card_of_nodup hn, he]

/-- Actual join reader calls, callbacks, snapshot copies, and outer control
iterations are charged to raw child and matching occurrence counts. -/
theorem collect_query_bounds (B : ℕ) :
    let N := (D.pair 0).outputUniverse.card + (D.pair 1).outputUniverse.card
    let Z := D.matchingUniverse.card
    (D.collect B).state.queries ≤ 6 * N + Z + 2 ∧
      (D.collect B).state.reports ≤ Z ∧
      B * (D.collect B).state.copies ≤ 2 * Z ∧
      (D.collect B).steps ≤ 6 * N + Z + 2 := by
  let report := RecordedDictionary.callback D.capacity (WeightEncoding.entryKey D.input) D.emit
  have hb := StreamJoin.run_bounds (D.pair 0).read (D.key 0) (D.pair 1).read (D.key 1)
    report (by intros; rfl) (D.pair 0).output (D.pair 0).read_law
    (D.pair 1).output (D.pair 1).read_law B (D.pair 0).lengthBound (D.pair 1).lengthBound
    ((D.pair 0).lengthBound + (D.pair 1).lengthBound + 1)
    (D.pair 0).start (D.pair 1).start RecordedDictionary.empty
    (D.pair 0).output_sorted (D.pair 1).output_sorted
    (D.pair 0).output_length_le (D.pair 1).output_length_le
  have hs := StreamJoin.stopped_steps_le_queries (D.pair 0).read (D.key 0)
    (D.pair 1).read (D.key 1) report B (D.pair 0).lengthBound (D.pair 1).lengthBound
    ((D.pair 0).lengthBound + (D.pair 1).lengthBound + 1)
    (D.pair 0).start (D.pair 1).start RecordedDictionary.empty
  rw [(D.pair 0).output_length_eq_card, (D.pair 1).output_length_eq_card,
    D.matching_potential_eq_card] at hb
  change (D.collect B).steps ≤ _ at hs
  have he := StreamJoin.stopped_eq (D.pair 0).read (D.key 0) (D.pair 1).read (D.key 1)
    report B (D.pair 0).lengthBound (D.pair 1).lengthBound
    ((D.pair 0).lengthBound + (D.pair 1).lengthBound + 1)
    (D.pair 0).start (D.pair 1).start RecordedDictionary.empty
  change (D.collect B).state = _ at he
  rw [← he] at hb hs
  exact ⟨hb.1, hb.2.1, hb.2.2, hs.trans hb.1⟩

end RepresentationParentData
end LowSpaceSubsetSum

end OAI
