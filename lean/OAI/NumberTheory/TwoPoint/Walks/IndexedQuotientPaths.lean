import OAI.NumberTheory.TwoPoint.Walks.IndexedRuns
import OAI.NumberTheory.TwoPoint.Walks.ColumnWordGeometry

namespace OAI

/-! Actual indexed regular pieces give the paths used by the forest decoder. -/

namespace TwoPointCorrelations

open Finset

variable {K α ι : Type*} [Field K] [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
/-- Forgetting the omitted-label cut retains precisely the original constant
intervals. Renaming regular labels therefore supplies actual quotient run data. -/
theorem indexed_chain_quotient_data (D : Submodule K (α → K))
    (anchor : ι → (α → K) ⧸ D) (regularLabel : ι → α) (rename : α → ι)
    (label : ℕ → α) (coefficient : ℕ → K)
    (first : ℕ × α) (rest : List (ℕ × α))
    (hchain : (first :: rest).IsChain (IndexedRunStep label))
    (hname : ∀ p ∈ first :: rest, regularLabel (rename p.2) = p.2)
    (hline : ∀ p ∈ first :: rest,
      ∃ c : K, D.mkQ (formalDeparture label coefficient p.1) = anchor (rename p.2) +
        c • D.mkQ (Pi.basisFun K α (regularLabel (rename p.2))))
    (hnonzero : ∀ p q, p ∈ first :: rest → q ∈ first :: rest → p.1 < q.1 →
      (∀ t ∈ Ico p.1 q.1, label t = p.2) → (∑ t ∈ Ico p.1 q.1, coefficient t) ≠ 0) :
    QuotientRunData D anchor regularLabel label coefficient first.1 (rename first.2)
      (rest.map (fun p => (p.1, rename p.2))) := by
  induction rest generalizing first with
  | nil => trivial
  | cons next rest ih =>
      have hfirst : first ∈ first :: next :: rest := List.mem_cons_self
      have hnext : next ∈ first :: next :: rest := by simp
      rcases hchain.rel with ⟨hlt, _, _, hne, hconst⟩
      refine ⟨hlt.le, ?_, hnonzero first next hfirst hnext hlt hconst, ?_, hline next hnext, ?_⟩
      · intro t ht
        rw [hname first hfirst]
        exact hconst t ht
      · intro heq
        apply hne
        calc
          first.2 = regularLabel (rename first.2) := (hname first hfirst).symm
          _ = regularLabel (rename next.2) := congrArg regularLabel heq
          _ = next.2 := hname next hnext
      · apply ih next hchain.tail
        · intro p hp
          exact hname p (List.mem_cons_of_mem _ hp)
        · intro p hp
          exact hline p (List.mem_cons_of_mem _ hp)
        · intro p q hp hq
          exact hnonzero p q (List.mem_cons_of_mem _ hp) (List.mem_cons_of_mem _ hq)

/-- Every nonempty regular piece produced from an actual block has the
quotient path data. Its transitions are proved from the indexed scan. -/
theorem indexed_regular_piece_quotient_data (D : Submodule K (α → K))
    (anchor : ι → (α → K) ⧸ D) (regularLabel : ι → α) (rename : α → ι)
    (label : ℕ → α) (coefficient : ℕ → K) (start len : ℕ)
    (omitted : α → Bool) (first : ℕ × α) (rest : List (ℕ × α))
    (hpiece : Sum.inl (first :: rest) ∈ partitionColumnRuns (fun p => omitted p.2)
      (indexedBlockRuns label start len))
    (hname : ∀ z, omitted z = false → regularLabel (rename z) = z)
    (hline : ∀ t ∈ Ico start (start + len), omitted (label t) = false →
      ∃ c : K, D.mkQ (formalDeparture label coefficient t) = anchor (rename (label t)) +
        c • D.mkQ (Pi.basisFun K α (regularLabel (rename (label t)))))
    (hnonzero : ∀ a b z, start ≤ a → a < b → b ≤ start + len →
      (∀ t ∈ Ico a b, label t = z) → (∑ t ∈ Ico a b, coefficient t) ≠ 0) :
    QuotientRunData D anchor regularLabel label coefficient first.1 (rename first.2)
      (rest.map (fun p => (p.1, rename p.2))) := by
  have hinfix := partitionColumnRuns_regular_infix (fun p => omitted p.2)
    (indexedBlockRuns label start len) (first :: rest) hpiece
  have hmem : ∀ p ∈ first :: rest, p ∈ indexedBlockRuns label start len :=
    fun p hp => hinfix.sublist.subset hp
  have hreg := (partitionColumnRuns_regular_entries (fun p => omitted p.2)
    (indexedBlockRuns label start len) (first :: rest) hpiece).2
  apply indexed_chain_quotient_data D anchor regularLabel rename label coefficient first rest
    (partitionColumnRuns_regular_chain (IndexedRunStep label) _ _ _
      (indexedBlockRuns_chain label start len) hpiece)
  · intro p hp
    exact hname p.2 (hreg p hp)
  · intro p hp
    obtain ⟨hl, hu, he⟩ := indexedBlockRuns_mem label start len p (hmem p hp)
    simpa only [he] using hline p.1 (mem_Ico.mpr ⟨hl, hu⟩) (by rw [he]; exact hreg p hp)
  · intro p q hp hq hpq hconst
    obtain ⟨hl, _, _⟩ := indexedBlockRuns_mem label start len p (hmem p hp)
    obtain ⟨_, hu, _⟩ := indexedBlockRuns_mem label start len q (hmem q hq)
    exact hnonzero p.1 q.1 p.2 hl hpq hu.le hconst

end TwoPointCorrelations

end OAI
