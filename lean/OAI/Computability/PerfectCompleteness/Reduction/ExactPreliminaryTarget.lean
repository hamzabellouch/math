import OAI.Computability.PerfectCompleteness.Machines.EncodingLemmas
import OAI.Computability.PerfectCompleteness.Reduction.CanonicalNamedGame
import OAI.Computability.PerfectCompleteness.Reduction.CompletedVisitOrder
import OAI.Computability.PerfectCompleteness.Reduction.TargetGameLemmas

namespace OAI

section

namespace PerfectCompleteness.ExactPreliminaryTarget

open UniqueGamesTheorem.Foundations.Games
open CompletionSoundness CompletionSoundness.LegalProjectionGame
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n t v m : Nat} [NeZero m]
    (clauses : Fin m → SourceClause.NormalizedClause v) (rows repeats : Nat → Nat)
    (hn : 0 < n) (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1)) (δ : ℚ)

local notation "F" => FinitePreliminaryCompletion.blockFamily clauses branch n t rows repeats
local notation "q" => FinitePreliminaryCompletion.alphabet branch n t δ
local notation "family" => FinitePreliminaryCompletion.actualFamily
  (t := t) clauses rows repeats hn hbranch hrows δ
local notation "order" => CompletedVisitOrder.completedOrder
  (t := t) clauses rows repeats hn hbranch hrows δ
local notation "rawOrder" => CompletedVisitOrder.rawOrder
  (t := t) clauses rows repeats hn hbranch hrows δ
local notation "coverage" => CompletedVisitOrder.mem_rawOrder
  (t := t) clauses rows repeats hn hbranch hrows δ

local instance leftVertex_fintype : Fintype (CanonicalGame.LeftVertex F) := Fintype.ofFinite _
local instance rightVertex_fintype : Fintype (CanonicalGame.RightVertex F) := Fintype.ofFinite _
local instance leftLabel_fintype (x : CanonicalGame.LeftVertex F) :
    Fintype (CanonicalGame.LeftLabel F x) := Fintype.ofFinite _
local instance rightLabel_fintype (y : CanonicalGame.RightVertex F) :
    Fintype (CanonicalGame.RightLabel F y) := Fintype.ofFinite _
local instance rightAlphabet_nonempty : Nonempty (Fin q) :=
  ⟨⟨0, CanonicalLocalCompletion.alphabet_positive (TreeCanonical.locationCount branch n t) δ⟩⟩
local instance leftAlphabet_nonempty : Nonempty (Fin (2 * q)) :=
  ⟨⟨0, Nat.mul_pos (by decide)
    (CanonicalLocalCompletion.alphabet_positive (TreeCanonical.locationCount branch n t) δ)⟩⟩

def namedGame := CanonicalNamedGame.rename F rawOrder coverage (family).game

def entry (e : CompletedSignedLaw.Completed (t := t) clauses rows repeats hn hbranch hrows δ) :
    Edge (rawOrder).length (rawOrder).length q where
  left := (namedGame (t := t) clauses rows repeats hn hbranch hrows δ).left e
  right := (namedGame (t := t) clauses rows repeats hn hbranch hrows δ).right e
  projection := ProjectionTable.ofMap ((family).map e.1 e.2) (by
    intro b
    rw [Fintype.card_eq_nat_card]
    have h := (family).exact_two e.1 e.2 b
    rw [Fintype.card_eq_nat_card] at h
    exact h)

theorem entry_satisfied (e : CompletedSignedLaw.Completed (t := t) clauses rows repeats hn hbranch hrows δ)
    (a : Fin (rawOrder).length → Fin (2 * q)) (b : Fin (rawOrder).length → Fin q) :
    (entry (t := t) clauses rows repeats hn hbranch hrows δ e).satisfied a b =
      (namedGame (t := t) clauses rows repeats hn hbranch hrows δ).wins (a, b) e := by
  simp only [Edge.satisfied, entry, ProjectionTable.ofMap_apply]
  exact decide_eq_decide.mpr Iff.rfl

def construct : Instance q where
  leftVertices := (rawOrder).length
  rightVertices := (rawOrder).length
  edges := (order).map (entry (t := t) clauses rows repeats hn hbranch hrows δ)
  nonempty := by
    intro hempty
    have h := List.map_eq_nil_iff.mp hempty
    exact CompletedVisitOrder.completedOrder_nonempty
      (t := t) clauses rows repeats hn hbranch hrows δ h

theorem edge_count :
    (construct (t := t) clauses rows repeats hn hbranch hrows δ).edges.length =
      SignedMultiplicity.denominator branch n t rows repeats hn hbranch hrows q *
        m ^ TreeCanonical.locationCount branch n t := by
  change ((order).map (entry (t := t) clauses rows repeats hn hbranch hrows δ)).length = _
  rw [List.length_map]
  exact CompletedVisitOrder.completedOrder_length
    (t := t) clauses rows repeats hn hbranch hrows δ

theorem leftVertices_eq_edges :
    (construct (t := t) clauses rows repeats hn hbranch hrows δ).leftVertices =
      (construct (t := t) clauses rows repeats hn hbranch hrows δ).edges.length := by
  exact (CompletedVisitOrder.rawOrder_length
    (t := t) clauses rows repeats hn hbranch hrows δ).trans
    (edge_count (t := t) clauses rows repeats hn hbranch hrows δ).symm

theorem rightVertices_eq_edges :
    (construct (t := t) clauses rows repeats hn hbranch hrows δ).rightVertices =
      (construct (t := t) clauses rows repeats hn hbranch hrows δ).edges.length :=
  leftVertices_eq_edges (t := t) clauses rows repeats hn hbranch hrows δ

theorem rate_eq (a : Fin (rawOrder).length → Fin (2 * q)) (b : Fin (rawOrder).length → Fin q) :
    (countSatisfied a b (construct (t := t) clauses rows repeats hn hbranch hrows δ).edges : ℝ) /
        (construct (t := t) clauses rows repeats hn hbranch hrows δ).edges.length =
      (namedGame (t := t) clauses rows repeats hn hbranch hrows δ).success (a, b) := by
  change (countSatisfied a b
      ((order).map (entry (t := t) clauses rows repeats hn hbranch hrows δ)) : ℝ) /
    ((order).map (entry (t := t) clauses rows repeats hn hbranch hrows δ)).length = _
  rw [RoundedTarget.countSatisfied_eq_filter]
  simp only [List.filter_map, List.length_map, Function.comp_def]
  have h := CompletedVisitOrder.completedOrder_probability
    (t := t) clauses rows repeats hn hbranch hrows δ
    (fun e => (entry (t := t) clauses rows repeats hn hbranch hrows δ e).satisfied a b)
  simpa only [Function.comp_def, entry_satisfied, OccurrenceGame.success,
    namedGame, CanonicalNamedGame.rename_occurrences] using h

theorem value_eq :
    (construct (t := t) clauses rows repeats hn hbranch hrows δ).value =
      FinitePreliminaryCompletion.actualValue
        (t := t) clauses rows repeats hn hbranch hrows δ := by
  have hq : 0 < q :=
    CanonicalLocalCompletion.alphabet_positive (TreeCanonical.locationCount branch n t) δ
  have hnamed : (construct (t := t) clauses rows repeats hn hbranch hrows δ).value =
      (namedGame (t := t) clauses rows repeats hn hbranch hrows δ).value := by
    apply le_antisymm
    · obtain ⟨s, hs⟩ :=
        (construct (t := t) clauses rows repeats hn hbranch hrows δ).maxSatisfied_attained hq
      unfold Instance.value
      rw [← hs]
      exact (rate_eq (t := t) clauses rows repeats hn hbranch hrows δ s.1 s.2).le.trans
        ((namedGame (t := t) clauses rows repeats hn hbranch hrows δ).success_le_value s)
    · obtain ⟨s, hs⟩ :=
        (namedGame (t := t) clauses rows repeats hn hbranch hrows δ).exists_optimal_strategy
      calc
        (namedGame (t := t) clauses rows repeats hn hbranch hrows δ).value =
            (namedGame (t := t) clauses rows repeats hn hbranch hrows δ).success s := hs.symm
        _ = (countSatisfied s.1 s.2
            (construct (t := t) clauses rows repeats hn hbranch hrows δ).edges : ℝ) /
              (construct (t := t) clauses rows repeats hn hbranch hrows δ).edges.length :=
          (rate_eq (t := t) clauses rows repeats hn hbranch hrows δ s.1 s.2).symm
        _ ≤ (construct (t := t) clauses rows repeats hn hbranch hrows δ).value :=
          (construct (t := t) clauses rows repeats hn hbranch hrows δ).rate_le_value s
  exact hnamed.trans (CanonicalNamedGame.rename_value_eq F rawOrder coverage (family).game)

theorem value_le (hδ : 0 < δ) :
    (construct (t := t) clauses rows repeats hn hbranch hrows δ).value ≤
      (PreliminarySampler.game clauses branch n t rows repeats hn hbranch hrows).value +
        (δ : ℝ) / 3 := by
  rw [value_eq]
  exact FinitePreliminaryCompletion.actualValue_le
    (t := t) clauses rows repeats hn hbranch hrows δ hδ

theorem perfectlyComplete (assignment : Fin v → Bool)
    (hsat : ∀ c, (clauses c).clause.eval assignment = true) :
    PerfectlyComplete (construct (t := t) clauses rows repeats hn hbranch hrows δ) := by
  apply ((construct (t := t) clauses rows repeats hn hbranch hrows δ).perfectlyComplete_iff_value_eq_one
    (CanonicalLocalCompletion.alphabet_positive (TreeCanonical.locationCount branch n t) δ)).2
  rw [value_eq]
  exact FinitePreliminaryCompletion.actualValue_of_satisfying
    (t := t) clauses rows repeats hn hbranch hrows δ assignment hsat

theorem encoding_length_le :
    let target := construct (t := t) clauses rows repeats hn hbranch hrows δ
    let N := target.edges.length
    (Encoding.gameBits target).length ≤
      2 * N + q + N + 4 + N * (2 * N + 2 * q * q + 2 * q + 2) := by
  dsimp only
  have h := Encoding.gameBits_length_le_of_edge_count
    (construct (t := t) clauses rows repeats hn hbranch hrows δ)
    (construct (t := t) clauses rows repeats hn hbranch hrows δ).edges.length le_rfl
  have arithmetic (l r N : Nat) (hl : l = N) (hr : r = N) :
      l + r + q + N + 4 + N * (l + r + 2 * q * q + 2 * q + 2) =
        2 * N + q + N + 4 + N * (2 * N + 2 * q * q + 2 * q + 2) := by
    simp only [hl, hr, two_mul]
  exact h.trans_eq (arithmetic _ _ _
    (leftVertices_eq_edges (t := t) clauses rows repeats hn hbranch hrows δ)
    (rightVertices_eq_edges (t := t) clauses rows repeats hn hbranch hrows δ))

end
end PerfectCompleteness.ExactPreliminaryTarget

end

end OAI
