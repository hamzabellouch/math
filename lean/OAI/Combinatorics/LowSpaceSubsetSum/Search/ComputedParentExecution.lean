import OAI.Combinatorics.LowSpaceSubsetSum.Search.PreparedParentExecution
import OAI.Combinatorics.LowSpaceSubsetSum.Search.ComputedParentFuels
import OAI.Combinatorics.LowSpaceSubsetSum.Search.PreparedReaderBounds

namespace OAI

/-! # Executed parent setup, cached limits, and stopped collection -/

namespace LowSpaceSubsetSum.ComputedParentExecution

variable {n : ℕ}

def run (D : RepresentationParentData n) (F : IndexedMask n) (P : StoredRestriction n)
    (hF : F.semantic = D.signs) (B : ℕ) : PreparedParentExecution.Result D.input D.capacity × ℕ :=
  let limits := ComputedParentFuels.run D
  let out := PreparedParentExecution.collect D F P hF B
    limits.1.first limits.1.second limits.1.control
  (out.1, limits.2 + out.2 + 2)

theorem run_value (D : RepresentationParentData n) (F : IndexedMask n) (P : StoredRestriction n)
    (hF : F.semantic = D.signs) (B : ℕ) :
    (run D F P hF B).1 = PreparedParentExecution.project
      (StoredParentExecution.collect {D with maskRestriction := P.semantic} F hF B).1 := by
  apply PreparedParentExecution.collect_value
  · exact ComputedParentFuels.first_value D
  · exact ComputedParentFuels.second_value D
  · rw [ComputedParentFuels.control_value, ComputedParentFuels.first_value,
      ComputedParentFuels.second_value]

theorem dictionary_value (D : RepresentationParentData n) (F : IndexedMask n)
    (P : StoredRestriction n) (hF : F.semantic = D.signs) (B : ℕ) :
    StoredDictionaryJoin.erase D.input D.capacity (run D F P hF B).1.dictionary =
      ({D with maskRestriction := P.semantic}.collect B).state.user := by
  rw [run_value]
  have hv := congrArg (fun out => out.state.user)
    (StoredParentExecution.collect_value {D with maskRestriction := P.semantic} F hF B)
  exact hv

theorem run_work (D : RepresentationParentData n) (F : IndexedMask n) (P : StoredRestriction n)
    (hF : F.semantic = D.signs) (B C : ℕ) (hn : 10000 ≤ n)
    (hl : ∀ j, (D.pair j).left.occurrences.card ≤ C)
    (hr : ∀ j, (D.pair j).right.occurrences.card ≤ C) (hC : C ≤ 2 ^ n)
    (hcopy : (12 * n + 32) *
      2 ^ (Nat.clog 2 ({D with maskRestriction := P.semantic}.pair 1).leftArray.size + 1) ≤ B) :
    (run D F P hF B).2 ≤
      2 * inputScale D.input ^ 9 * (C + 1) + inputScale D.input ^ 3 + 7 +
      inputScale D.input ^ 6 * (({D with maskRestriction := P.semantic}.collect B).state.queries +
        ({D with maskRestriction := P.semantic}.collect B).state.reports + 1) +
      B * ({D with maskRestriction := P.semantic}.collect B).state.copies := by
  have hdepth (j : Fin 2) :
      Nat.clog 2 ({D with maskRestriction := P.semantic}.pair j).leftArray.size ≤ n := by
    have hd := PreparedReaderContext.build_depth D F P hF j ((hl j).trans hC)
    rw [PreparedReaderContext.build_value] at hd
    exact hd
  have hp := PreparedParentExecution.collect_work D F P hF B
    (ComputedParentFuels.run D).1.first (ComputedParentFuels.run D).1.second
    (ComputedParentFuels.run D).1.control C
    (ComputedParentFuels.first_value D) (ComputedParentFuels.second_value D)
    (by rw [ComputedParentFuels.control_value, ComputedParentFuels.first_value,
      ComputedParentFuels.second_value]) hn hl hr hC (hdepth 0) (hdepth 1) hcopy
  have hf := ComputedParentFuels.run_scale D hn
  change (ComputedParentFuels.run D).2 +
    (PreparedParentExecution.collect D F P hF B (ComputedParentFuels.run D).1.first
      (ComputedParentFuels.run D).1.second (ComputedParentFuels.run D).1.control).2 + 2 ≤ _
  omega

end LowSpaceSubsetSum.ComputedParentExecution

end OAI
