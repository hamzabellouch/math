import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationQueryBound
import OAI.Combinatorics.LowSpaceSubsetSum.Compression.CompressionTrialLedger

namespace OAI

/-! # Actual parent-join counters through the full prefix tree

The full tree is only an accounting view. The executable search is depth
first and may return YES earlier. Invalid matching tuples remain charged.
-/

noncomputable section

namespace LowSpaceSubsetSum

namespace CompressionLedger

def add (a b : CompressionLedger) : CompressionLedger :=
  ⟨a.queries + b.queries, a.reports + b.reports,
    a.copies + b.copies, a.controls + b.controls⟩

end CompressionLedger

namespace RepresentationParentData

variable {n : ℕ} (D : RepresentationParentData n)

def localLedger (B : ℕ) : CompressionLedger :=
  ⟨(D.collect B).state.queries, (D.collect B).state.reports,
    (D.collect B).state.copies, (D.collect B).steps⟩

def prefixLedger (B : ℕ) : List (Fin n) → MaskRestriction n → CompressionLedger
  | [], P => ({ D with maskRestriction := P }).localLedger B
  | i :: order, P =>
    let task :=  ({ D with maskRestriction := P }).localLedger B
    if ({ D with maskRestriction := P }.collect B).state.user.keys.overflow then
      task.add ((prefixLedger B order (P.force i false)).add
        (prefixLedger B order (P.force i true)))
    else task

theorem prefixLedger_queries (B : ℕ) (order : List (Fin n)) (P : MaskRestriction n) :
    (D.prefixLedger B order P).queries = D.queryVisits B order P := by
  induction order generalizing P with
  | nil => rfl
  | cons i order ih =>
    simp only [prefixLedger, queryVisits]
    split <;> simp only [CompressionLedger.add, localLedger, ih, Nat.add_zero]

theorem prefixLedger_bounds (B : ℕ) (order : List (Fin n)) (P : MaskRestriction n) :
    (D.prefixLedger B order P).reports ≤ D.matchingVisits B order P ∧
      B * (D.prefixLedger B order P).copies ≤ 2 * D.matchingVisits B order P ∧
      (D.prefixLedger B order P).controls ≤ (D.prefixLedger B order P).queries := by
  induction order generalizing P with
  | nil =>
    have h := ({ D with maskRestriction := P }).collect_query_bounds B
    have hstep : ({ D with maskRestriction := P }.collect B).steps ≤
        ({ D with maskRestriction := P }.collect B).state.queries := by
      simpa only [RepresentationParentData.collect, StreamJoin.stopped_eq] using
        StreamJoin.stopped_steps_le_queries _ _ _ _ _ _ _ _ _ _ _ _
    exact ⟨h.2.1, h.2.2.1, hstep⟩
  | cons i order ih =>
    have h := ({ D with maskRestriction := P }).collect_query_bounds B
    have hstep : ({ D with maskRestriction := P }.collect B).steps ≤
        ({ D with maskRestriction := P }.collect B).state.queries := by
      simpa only [RepresentationParentData.collect, StreamJoin.stopped_eq] using
        StreamJoin.stopped_steps_le_queries _ _ _ _ _ _ _ _ _ _ _ _
    have h0 := ih (P.force i false)
    have h1 := ih (P.force i true)
    simp only [prefixLedger, matchingVisits]
    split <;> simp only [CompressionLedger.add, localLedger, Nat.mul_add]
    · exact ⟨Nat.add_le_add h.2.1 (Nat.add_le_add h0.1 h1.1),
        Nat.add_le_add h.2.2.1 (Nat.add_le_add h0.2.1 h1.2.1),
        Nat.add_le_add hstep (Nat.add_le_add h0.2.2 h1.2.2)⟩
    · simpa only [Nat.add_zero] using ⟨h.2.1, h.2.2.1, hstep⟩

end RepresentationParentData
end LowSpaceSubsetSum

end

end OAI
