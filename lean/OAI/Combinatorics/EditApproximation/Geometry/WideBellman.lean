import OAI.Combinatorics.EditApproximation.Geometry.ActualActionValues
import OAI.Combinatorics.EditApproximation.Geometry.WideActions
import OAI.Combinatorics.EditApproximation.Geometry.Bellman

namespace OAI

/-! Bellman cones of the actual labeled finite wide actions preserve both lower invariants. -/

namespace EditApproximation

open Finset

noncomputable def actualWideActions {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P : ℕ) :
    List (BellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M) :=
  representatives.flatMap fun br => (wideActionList M parent br.2 br.1 P).map fun states =>
    ⟨br.2, endpointActionConnection br.2 states, fun i => (i, states i)⟩

noncomputable def actualWideBellman {nx ny M : ℕ} (parent : TargetInterval nx)
    (representatives : List (ℕ × TargetInterval ny)) (P : ℕ)
    (initial : TargetInterval ny → ℝ) (L : ℝ)
    (child : Fin M → TargetInterval ny → ℝ) (q : TargetInterval ny) : ℝ :=
  finiteBellman initial (fun q r => targetEndpointDistance q r) L
    (actualWideActions parent representatives P) (fun is => child is.1 is.2) q

theorem actual_coned_action_lower {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (parent : TargetInterval source.length)
    (q r : TargetInterval target.length) (states : Fin M → TargetInterval target.length)
    (a L : ℝ) (ha : 1 ≤ a) (hL : 1 ≤ L)
    (child : Fin M → TargetInterval target.length → ℝ)
    (hchild : ∀ i s, max ((stateEditCost
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target s : ℝ) / a)
        |stateLengthGap (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target s| ≤
          child i s) :
    max ((stateEditCost (substring source parent.lo parent.hi) target q : ℝ) / a)
      |stateLengthGap (substring source parent.lo parent.hi) target q| ≤
        L * targetEndpointDistance q r + endpointActionValue r states child := by
  have hcenter := actual_endpoint_action_lower source target hM parent r states a ha child
    (fun i => (le_max_left _ _).trans (hchild i (states i)))
    (fun i => (le_max_right _ _).trans (hchild i (states i)))
  have hcost := (le_max_left _ _).trans hcenter
  have hgap := (le_max_right _ _).trans hcenter
  have ha0 : 0 < a := by linarith
  have hdist0 : (0 : ℝ) ≤ targetEndpointDistance q r := Nat.cast_nonneg _
  have hcharge : (targetEndpointDistance q r : ℝ) ≤ L * targetEndpointDistance q r := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hL hdist0
  apply max_le
  · have hspatial : (stateEditCost (substring source parent.lo parent.hi) target q : ℝ) ≤
        stateEditCost (substring source parent.lo parent.hi) target r + targetEndpointDistance q r := by
      exact_mod_cast stateEditCost_spatial (substring source parent.lo parent.hi) target q r
    have hscaled := div_le_div_of_nonneg_right hspatial ha0.le
    have hdiv : (targetEndpointDistance q r : ℝ) / a ≤ targetEndpointDistance q r := by
      apply (div_le_iff₀ ha0).2
      simpa only [one_mul, mul_one, mul_comm] using mul_le_mul_of_nonneg_right ha hdist0
    rw [add_div] at hscaled
    linarith
  · have hspatial := stateLengthGap_spatial (substring source parent.lo parent.hi) target q r
    linarith

theorem actualWideBellman_lower {α : Type*} (source target : List α)
    {M : ℕ} (hM : 0 < M) (parent : TargetInterval source.length)
    (representatives : List (ℕ × TargetInterval target.length)) (P : ℕ)
    (initial : TargetInterval target.length → ℝ) (a L : ℝ) (ha : 1 ≤ a) (hL : 1 ≤ L)
    (child : Fin M → TargetInterval target.length → ℝ)
    (hinit : ∀ q, max ((stateEditCost (substring source parent.lo parent.hi) target q : ℝ) / a)
      |stateLengthGap (substring source parent.lo parent.hi) target q| ≤ initial q)
    (hchild : ∀ i s, max ((stateEditCost
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target s : ℝ) / a)
        |stateLengthGap (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target s| ≤
          child i s) (q : TargetInterval target.length) :
    max ((stateEditCost (substring source parent.lo parent.hi) target q : ℝ) / a)
      |stateLengthGap (substring source parent.lo parent.hi) target q| ≤
        actualWideBellman parent representatives P initial L child q := by
  apply finiteBellman_lower initial _ _ _ _ _ hinit
  intro query action haction
  obtain ⟨br, hbr, haction⟩ := List.mem_flatMap.mp haction
  obtain ⟨states, hstates, rfl⟩ := List.mem_map.mp haction
  simpa only [bellmanActionValue, endpointActionValue, add_assoc] using
    actual_coned_action_lower source target hM parent query br.2 states a L ha hL child hchild

end EditApproximation

end OAI
