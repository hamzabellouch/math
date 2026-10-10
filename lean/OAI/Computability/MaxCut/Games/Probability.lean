import Mathlib
import OAI.Computability.MaxCut.Games.Incidence

namespace OAI

namespace MaxCutGames.Reduction.SourceProbability

open ActualSource

theorem Source_failure_eq_count (S : Source) (A : Fin S.«variables» → Bool) :
    S.failure A =
      (S.sourceList.countP (fun e => !CloneGap.satisfied e A) : ℚ) / S.occurrences := by
  have hp := IncidenceProbability.expect_bool_indicator_eq_count_ofFn
    (fun i : Fin S.occurrences => !S.satisfied A i)
  have he : Finset.univ.expect
      (fun i : Fin S.occurrences => if !S.satisfied A i then (1 : ℚ) else 0) =
      S.failure A := by
    unfold Source.failure
    congr 1
    funext i
    cases S.satisfied A i <;> rfl
  rw [he] at hp
  rw [hp]
  congr 2
  have hmap : List.ofFn (fun i : Fin S.occurrences => !S.satisfied A i) =
      S.sourceList.map (fun e => !CloneGap.satisfied e A) := by
    simp only [Source.sourceList, List.map_ofFn, Source.satisfied, Function.comp_def]
  rw [hmap, List.countP_map]
  rfl

theorem ofList_failure {n : Nat} (es : List (CloneGap.Equation (Fin n)))
    (hne : es ≠ []) (A : Fin n → Bool) :
    (Source.ofList es hne).failure A =
      (es.countP (fun e => !CloneGap.satisfied e A) : ℚ) / es.length := by
  have h := Source_failure_eq_count (Source.ofList es hne) A
  simpa [Source.sourceList, Source.ofList] using h

theorem count_complement {α : Type*} (es : List α) (p : α → Bool) :
    es.countP (fun e => !p e) + es.countP p = es.length := by
  induction es with
  | nil => simp
  | cons e es ih =>
    cases hp : p e <;> simp [hp] at * <;> omega

theorem failure_add_satisfaction (S : Source) (A : Fin S.«variables» → Bool) :
    S.failure A +
      (S.sourceList.countP (fun e => CloneGap.satisfied e A) : ℚ) / S.occurrences = 1 := by
  rw [Source_failure_eq_count, ← add_div]
  have h := count_complement S.sourceList (fun e => CloneGap.satisfied e A)
  have hc : ((S.sourceList.countP (fun e => !CloneGap.satisfied e A) : ℚ) +
      (S.sourceList.countP (fun e => CloneGap.satisfied e A) : ℚ)) = S.occurrences := by
    exact_mod_cast (h.trans S.sourceList_length)
  rw [hc, div_self]
  exact_mod_cast Nat.ne_of_gt S.nonempty

theorem quarter_gap_iff (S : Source) (A : Fin S.«variables» → Bool) :
    (1 / 4 : ℚ) ≤ S.failure A ↔
      S.sourceList.length ≤ 4 * S.sourceList.countP (fun e => !CloneGap.satisfied e A) := by
  rw [Source_failure_eq_count]
  have hn : (0 : ℚ) < S.occurrences := by exact_mod_cast S.nonempty
  rw [le_div_iff₀ hn]
  constructor
  · intro h
    have h' : (S.occurrences : ℚ) ≤ 4 *
        (S.sourceList.countP (fun e => !CloneGap.satisfied e A) : ℚ) := by linarith
    rw [S.sourceList_length]
    exact_mod_cast h'
  · intro h
    rw [S.sourceList_length] at h
    have h' : (S.occurrences : ℚ) ≤ 4 *
        (S.sourceList.countP (fun e => !CloneGap.satisfied e A) : ℚ) := by exact_mod_cast h
    linarith

end MaxCutGames.Reduction.SourceProbability

end OAI
