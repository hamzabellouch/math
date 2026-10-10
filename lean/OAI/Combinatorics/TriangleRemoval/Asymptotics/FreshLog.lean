import Mathlib
import OAI.Combinatorics.TriangleRemoval.Queries.TreeBind

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SharpTerminalLeave.ExposureTree
open scoped BigOperators

variable {K V O P : Type*}

noncomputable def freshLog (ν : K → PMF V) : ExposureTree K V O → PMF (O × List K)
  | .done o => PMF.pure (o, [])
  | .ask k f => (ν k).bind (fun v =>
      (freshLog ν (f v)).map (fun z => (z.1, k :: z.2)))

def repeats [DecidableEq K] : Finset K → List K → Bool
  | _, [] => false
  | seen, k :: ks => decide (k ∈ seen) || repeats (insert k seen) ks

@[simp] theorem repeats_cons [DecidableEq K] (seen : Finset K) (k : K) (ks : List K) :
    repeats seen (k :: ks) = (decide (k ∈ seen) || repeats (insert k seen) ks) := rfl

theorem repeats_false_iff [DecidableEq K] (seen : Finset K) (ks : List K) :
    repeats seen ks = false ↔ ks.Nodup ∧ ∀ k ∈ ks, k ∉ seen := by
  induction ks generalizing seen with
  | nil => simp [repeats]
  | cons k ks ih =>
    simp only [repeats_cons, Bool.or_eq_false_iff, decide_eq_false_iff_not,
      ih, List.nodup_cons, List.mem_cons, Finset.mem_insert, not_or]
    constructor
    · rintro ⟨hk, hnd, hh⟩
      refine ⟨⟨?_, hnd⟩, ?_⟩
      · intro hmem
        exact (hh k hmem).1 rfl
      · intro a ha
        rcases ha with rfl | ha
        · exact hk
        · exact (hh a ha).2
    · rintro ⟨⟨hkm,hnd⟩, hh⟩
      refine ⟨hh k (Or.inl rfl), hnd, ?_⟩
      intro a ha
      refine ⟨?_, hh a (Or.inr ha)⟩
      intro hak
      exact hkm (hak ▸ ha)

@[simp] theorem repeats_empty_false_iff [DecidableEq K] (ks : List K) :
    repeats ∅ ks = false ↔ ks.Nodup := by simp [repeats_false_iff]

@[simp] theorem freshLog_outcome (ν : K → PMF V) (A : ExposureTree K V O) :
    (freshLog ν A).map Prod.fst = fresh ν A := by
  induction A with
  | done o => simp [freshLog, fresh, PMF.pure_map]
  | ask k f ih =>
    simp only [freshLog, PMF.map_bind, PMF.map_comp, fresh]
    congr 1
    funext v
    exact ih v

theorem freshRecorded_eq_log [DecidableEq K] (ν : K → PMF V)
    (A : ExposureTree K V O) (seen : Finset K) :
    freshRecorded ν A seen =
      (freshLog ν A).map (fun z => (z.1, repeats seen z.2)) := by
  induction A generalizing seen with
  | done o => simp [freshRecorded, freshLog, repeats, PMF.pure_map]
  | ask k f ih =>
    simp only [freshRecorded, freshLog, PMF.map_bind, PMF.map_comp]
    congr 1
    funext v
    by_cases hk : k ∈ seen
    · simp only [ite_eq_left hk, ih, PMF.map_comp]
      congr 1
      funext z
      simp [repeats, hk]
    · simp only [ite_eq_right hk, ih]
      congr 1
      funext z
      simp [repeats, hk]

theorem freshLog_bind (ν : K → PMF V) (A : ExposureTree K V O)
    (f : O → ExposureTree K V P) :
    freshLog ν (bind A f) =
      (freshLog ν A).bind (fun z =>
        (freshLog ν (f z.1)).map (fun y => (y.1, z.2 ++ y.2))) := by
  induction A with
  | done o =>
    simp only [bind, freshLog, PMF.pure_bind, List.nil_append]
    exact (PMF.map_id _).symm
  | ask k g ih =>
    simp only [bind, freshLog, ih, PMF.bind_bind, PMF.map_bind, PMF.bind_map,
      PMF.map_comp]
    congr 1

end SharpTerminalLeave.ExposureTree

end

end OAI
