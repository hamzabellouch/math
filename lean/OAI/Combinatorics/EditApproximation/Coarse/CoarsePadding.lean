import OAI.Combinatorics.EditApproximation.Geometry.Geometry
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# Fresh-symbol right padding

Padding uses `none`, while original letters are tagged by `some`. Removing
the fresh symbols contracts every unrestricted unit-cost edit script.
-/

namespace EditApproximation

open EditDistortion

universe u v

/-- Removing or relabeling letters replaces each edit by at most one edit. -/
theorem step_filterMap_script {α : Type u} {β : Type v} {s : Bool}
    (f : α → Option β) {x y : List α} (step : Step s x y) :
    ∃ n ≤ 1, Script s n (x.filterMap f) (y.filterMap f) := by
  cases step with
  | insert before after letter =>
    cases hletter : f letter with
    | none => exact ⟨0, by omega, by simpa [hletter] using Script.nil ((before ++ after).filterMap f)⟩
    | some b => exact ⟨1, le_rfl, by simpa [hletter] using (Script.single (Step.insert (substitutions := s) (before.filterMap f) (after.filterMap f) b))⟩
  | delete before after letter =>
    cases hletter : f letter with
    | none => exact ⟨0, by omega, by simpa [hletter] using Script.nil ((before ++ after).filterMap f)⟩
    | some b => exact ⟨1, le_rfl, by simpa [hletter] using (Script.single (Step.delete (substitutions := s) (before.filterMap f) (after.filterMap f) b))⟩
  | substitute hs before after a b =>
    cases ha : f a with
    | none =>
      cases hb : f b with
      | none => exact ⟨0, by omega, by simpa [ha, hb] using Script.nil ((before ++ after).filterMap f)⟩
      | some b' => exact ⟨1, le_rfl, by simpa [ha, hb] using (Script.single (Step.insert (substitutions := s) (before.filterMap f) (after.filterMap f) b'))⟩
    | some a' =>
      cases hb : f b with
      | none => exact ⟨1, le_rfl, by simpa [ha, hb] using (Script.single (Step.delete (substitutions := s) (before.filterMap f) (after.filterMap f) a'))⟩
      | some b' => exact ⟨1, le_rfl, by simpa [ha, hb] using (Script.single (Step.substitute hs (before.filterMap f) (after.filterMap f) a' b'))⟩

theorem script_filterMap {α : Type u} {β : Type v} {s : Bool}
    (f : α → Option β) {n : ℕ} {x y : List α} (script : Script s n x y) :
    ∃ m ≤ n, Script s m (x.filterMap f) (y.filterMap f) := by
  induction script with
  | nil word => exact ⟨0, le_rfl, .nil _⟩
  | cons step script ih =>
    obtain ⟨m, hm, hscript⟩ := ih
    obtain ⟨l, hl, hstep⟩ := step_filterMap_script f step
    exact ⟨l + m, by omega, hstep.trans hscript⟩

theorem edit_filterMap_le {α : Type u} {β : Type v}
    (f : α → Option β) (x y : List α) :
    edit (x.filterMap f) (y.filterMap f) ≤ edit x y := by
  obtain ⟨m, hm, hscript⟩ := script_filterMap f (cost_spec (s := true) x y)
  exact (cost_le hscript).trans hm

/-- Right padding to a prescribed common width with a fresh tagged letter. -/


theorem coarsePadTo_length {α : Type u} (n : ℕ) (word : List α) (h : word.length ≤ n) :
    (coarsePadTo n word).length = n := by
  simp only [coarsePadTo, List.length_append, List.length_map, List.length_replicate]
  omega

theorem coarsePadTo_remove {α : Type u} (n : ℕ) (word : List α) :
    (coarsePadTo n word).filterMap id = word := by
  simp [coarsePadTo, List.filterMap_map]

/-- The actual padded instance has distance between the original distance
and twice that distance, including empty and unequal-length inputs. -/
theorem coarsePadding_distance_bounds {α : Type u} (x y : List α) :
    edit x y ≤ edit (coarsePadTo (max x.length y.length) x)
      (coarsePadTo (max x.length y.length) y) ∧
    edit (coarsePadTo (max x.length y.length) x)
      (coarsePadTo (max x.length y.length) y) ≤ 2 * edit x y := by
  constructor
  · have h := edit_filterMap_le id (coarsePadTo (max x.length y.length) x)
      (coarsePadTo (max x.length y.length) y)
    simpa only [coarsePadTo_remove] using h
  · have hlength := cost_length_bounds (s := true) x y
    change x.length ≤ y.length + edit x y ∧ y.length ≤ x.length + edit x y at hlength
    have htail : edit
        (List.replicate (max x.length y.length - x.length) (none : Option α))
        (List.replicate (max x.length y.length - y.length) none) ≤ edit x y := by
      have h := edit_le_max_length
        (List.replicate (max x.length y.length - x.length) (none : Option α))
        (List.replicate (max x.length y.length - y.length) none)
      simp only [List.length_replicate] at h
      rcases le_total x.length y.length with hxy | hyx
      · rw [max_eq_right hxy] at h ⊢
        omega
      · rw [max_eq_left hyx] at h ⊢
        omega
    have hmap := cost_map_le (s := true) some x y
    change edit (x.map some) (y.map some) ≤ edit x y at hmap
    have happend := cost_append_le (s := true) (x.map some) (y.map some)
      (List.replicate (max x.length y.length - x.length) none)
      (List.replicate (max x.length y.length - y.length) none)
    change edit (coarsePadTo (max x.length y.length) x)
      (coarsePadTo (max x.length y.length) y) ≤
        edit (x.map some) (y.map some) +
          edit (List.replicate (max x.length y.length - x.length) none)
            (List.replicate (max x.length y.length - y.length) none) at happend
    exact happend.trans (by omega)

end EditApproximation

end OAI
