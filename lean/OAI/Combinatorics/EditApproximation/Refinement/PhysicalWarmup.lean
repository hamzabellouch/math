import OAI.Combinatorics.EditApproximation.Geometry.StateDomain
import OAI.Combinatorics.EditApproximation.Geometry.WideBellman
import OAI.Combinatorics.EditApproximation.Numerics.RationalRefinement
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# Warmup on physical node labels

The Bellman operator requests only physical children. Distinct child labels
are retained even at repeated cuts. Nodes at the last physical level, and
source intervals of width at most one, retain their initial value.
-/

namespace EditApproximation









theorem physicalSourceInterval_child {M J nx : ℕ} (node : PhysicalNode M J)
    (hbelow : node.1.val < J) (i : Fin M) :
    physicalSourceInterval nx (physicalChild node hbelow i) = sourceChild (physicalSourceInterval nx node) i := rfl

noncomputable def physicalLower {α : Type*} {M J : ℕ} (source target : List α) (a : ℝ)
    (state : PhysicalEntry M J target.length) : ℝ :=
  max ((stateEditCost (physicalSource source state.1) target state.2 : ℝ) / a)
    |stateLengthGap (physicalSource source state.1) target state.2|

noncomputable def physicalBellman {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℝ) (initial : PhysicalEntry M J target.length → ℝ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (value : PhysicalEntry M J target.length → ℝ) (state : PhysicalEntry M J target.length) : ℝ := by
  classical
  let parent := physicalSourceInterval source.length state.1
  exact if hbelow : state.1.1.val < J then
    if parent.hi - parent.lo ≤ 1 then initial state else
      actualWideBellman parent (representatives state.1) P (fun q => initial (state.1, q)) L
        (fun i q => value (physicalChild state.1 hbelow i, q)) state.2
    else initial state

theorem physicalBellman_monotone {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℝ) (initial : PhysicalEntry M J target.length → ℝ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length)) :
    Monotone (physicalBellman source target P L initial representatives) := by
  classical
  intro value value' hvalue state
  unfold physicalBellman
  dsimp only
  split_ifs
  · exact le_rfl
  · apply finiteBellman_mono
    intro is
    exact hvalue _
  · exact le_rfl

theorem physicalBellman_le_initial {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℝ) (initial : PhysicalEntry M J target.length → ℝ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (value : PhysicalEntry M J target.length → ℝ) :
    physicalBellman source target P L initial representatives value ≤ initial := by
  classical
  intro state
  unfold physicalBellman
  dsimp only
  split_ifs
  · exact le_rfl
  · exact finiteBellman_le_fallback _ _ _ _ _ _
  · exact le_rfl

theorem physicalBellman_lower {α : Type*} {M J : ℕ} (source target : List α)
    (hM : 0 < M) (P : ℕ) (a L : ℝ) (ha : 1 ≤ a) (hL : 1 ≤ L)
    (initial : PhysicalEntry M J target.length → ℝ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (hinit : physicalLower source target a ≤ initial)
    (value : PhysicalEntry M J target.length → ℝ) (hvalue : physicalLower source target a ≤ value) :
    physicalLower source target a ≤ physicalBellman source target P L initial representatives value := by
  classical
  intro state
  unfold physicalBellman
  dsimp only
  split_ifs with hbelow hleaf
  · exact hinit state
  · apply actualWideBellman_lower source target hM _ _ P _ a L ha hL _
    · intro q
      exact hinit (state.1, q)
    · intro i q
      exact hvalue (physicalChild state.1 hbelow i, q)
  · exact hinit state

noncomputable def physicalWarmup {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℝ) (initial : PhysicalEntry M J target.length → ℝ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length)) :
    ℕ → PhysicalEntry M J target.length → ℝ :=
  warmup (physicalBellman source target P L initial representatives) initial

noncomputable def physicalWarmupAverage {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℝ) (initial : PhysicalEntry M J target.length → ℝ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (T : ℕ) : PhysicalEntry M J target.length → ℝ :=
  warmupAverage (physicalBellman source target P L initial representatives) initial T

theorem physicalBellman_le_action {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℝ) (initial : PhysicalEntry M J target.length → ℝ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (value : PhysicalEntry M J target.length → ℝ) (node : PhysicalNode M J)
    (hbelow : node.1.val < J) (hleaf : ¬ (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1)
    (q r : TargetInterval target.length) (b : ℕ)
    (hrep : (b, r) ∈ representatives node)
    (states : Fin M → TargetInterval target.length)
    (hstates : states ∈ wideActionList M (physicalSourceInterval source.length node) r b P) :
    physicalBellman source target P L initial representatives value (node, q) ≤
      L * targetEndpointDistance q r + endpointActionConnection r states +
        ∑ i, value (physicalChild node hbelow i, states i) := by
  classical
  unfold physicalBellman
  dsimp only
  rw [dite_eq_left hbelow, ite_eq_right hleaf]
  let action : BellmanAction (TargetInterval target.length) (Fin M × TargetInterval target.length) M :=
    ⟨r, endpointActionConnection r states, fun i => (i, states i)⟩
  have haction : action ∈ actualWideActions (physicalSourceInterval source.length node)
      (representatives node) P := by
    apply List.mem_flatMap.mpr
    refine ⟨(b, r), hrep, ?_⟩
    exact List.mem_map.mpr ⟨states, hstates, rfl⟩
  exact finiteBellman_le_action (fun s => initial (node, s))
    (fun s t => targetEndpointDistance s t) L
    (actualWideActions (physicalSourceInterval source.length node) (representatives node) P)
    (fun is => value (physicalChild node hbelow is.1, is.2)) q action haction

theorem physicalWarmup_average_sandwich {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℝ) (initial : PhysicalEntry M J target.length → ℝ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (T : ℕ) (hT : 0 < T) (state : PhysicalEntry M J target.length) :
    physicalWarmup source target P L initial representatives T state ≤
        physicalWarmupAverage source target P L initial representatives T state ∧
      physicalWarmupAverage source target P L initial representatives T state ≤ initial state :=
  warmup_average_sandwich _ _ T hT
    (physicalBellman_monotone source target P L initial representatives)
    (physicalBellman_le_initial source target P L initial representatives initial) state

theorem physicalWarmup_average_action_bound {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℝ) (initial : PhysicalEntry M J target.length → ℝ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (T : ℕ) (hT : 0 < T) (node : PhysicalNode M J)
    (hbelow : node.1.val < J) (hleaf : ¬ (physicalSourceInterval source.length node).hi -
      (physicalSourceInterval source.length node).lo ≤ 1)
    (q r : TargetInterval target.length) (b : ℕ)
    (hrep : (b, r) ∈ representatives node)
    (states : Fin M → TargetInterval target.length)
    (hstates : states ∈ wideActionList M (physicalSourceInterval source.length node) r b P) :
    physicalWarmupAverage source target P L initial representatives T (node, q) -
        (initial (node, q) - physicalWarmup source target P L initial representatives T (node, q)) / T ≤
      L * targetEndpointDistance q r + endpointActionConnection r states +
        ∑ i, physicalWarmupAverage source target P L initial representatives T
          (physicalChild node hbelow i, states i) := by
  apply warmup_average_action_bound _ _ T hT (node, q)
    (fun i => (physicalChild node hbelow i, states i))
    (L * targetEndpointDistance q r + endpointActionConnection r states)
  intro t _
  exact physicalBellman_le_action source target P L initial representatives _ node hbelow hleaf q r b hrep states hstates

theorem physicalWarmup_nonincreasing {α : Type*} {M J : ℕ} (source target : List α)
    (P : ℕ) (L : ℝ) (initial : PhysicalEntry M J target.length → ℝ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length)) :
    ∀ t, physicalWarmup source target P L initial representatives (t + 1) ≤
      physicalWarmup source target P L initial representatives t :=
  warmup_nonincreasing _ _ (physicalBellman_monotone source target P L initial representatives)
    (physicalBellman_le_initial source target P L initial representatives initial)

theorem physicalWarmup_lower {α : Type*} {M J : ℕ} (source target : List α)
    (hM : 0 < M) (P : ℕ) (a L : ℝ) (ha : 1 ≤ a) (hL : 1 ≤ L)
    (initial : PhysicalEntry M J target.length → ℝ)
    (representatives : PhysicalNode M J → List (ℕ × TargetInterval target.length))
    (hinit : physicalLower source target a ≤ initial) :
    ∀ t, physicalLower source target a ≤ physicalWarmup source target P L initial representatives t :=
  warmup_lower _ _ _ hinit
    (fun value hvalue => physicalBellman_lower source target hM P a L ha hL initial representatives hinit value hvalue)

end EditApproximation

end OAI
