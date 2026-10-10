import OAI.Combinatorics.EditApproximation.Geometry.RefinementConeLocality
import OAI.Combinatorics.EditApproximation.Geometry.LocalCells
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalSpatial
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Direct local enumeration computes the complete refinement Bellman cone
on a spatially regular initial table. Its finite definition applies to every seed. -/

namespace EditApproximation

open Finset



theorem representativeList_conditions {n N P F : ℕ} (a : ℚ)
    (initial : TargetInterval n → ℚ) {b : ℕ} {r : TargetInterval n}
    (hrep : (b, r) ∈ representativeList N P F a initial) :
    b ∈ dyadicScales N ∧ seedGridSpacing b P ∣ r.lo ∧ seedGridSpacing b P ∣ r.hi ∧
      (b : ℚ) / (4 * a) ≤ initial r ∧ initial r ≤ 8 * F * b := by
  obtain ⟨b', hb', hrep⟩ := List.mem_flatMap.mp hrep
  obtain ⟨r', hr', heq⟩ := List.mem_map.mp hrep
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  exact ⟨hb', of_decide_eq_true (List.mem_filter.mp hr').2⟩

theorem localRefinementRepresentatives_subset {n : ℕ} (N P F : ℕ) (a : ℚ)
    (initial : TargetInterval n → ℚ) (q : TargetInterval n) :
    ∀ br ∈ localRefinementRepresentatives N P F a initial q,
      br ∈ representativeList N P F a initial := by
  intro br hbr
  obtain ⟨b, hb, hbr⟩ := List.mem_flatMap.mp hbr
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hbr
  obtain ⟨hr, heligible⟩ := List.mem_filter.mp hr
  have hgrid := localTargetStates_on_grid q r hr
  exact representativeList_mem a initial r (List.mem_filter.mp hb).1 hgrid
    (of_decide_eq_true heligible).1 (of_decide_eq_true heligible).2

theorem rationalActualWideActions_representative {nx ny M : ℕ}
    (parent : TargetInterval nx) (representatives : List (ℕ × TargetInterval ny)) (P : ℕ)
    (action : RationalBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M)
    (ha : action ∈ rationalActualWideActions parent representatives P) :
    ∃ b, (b, action.center) ∈ representatives := by
  obtain ⟨br, hbr, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨states, _, heq⟩ := List.mem_map.mp ha
  exact ⟨br.1, (congrArg (fun a => (br.1, a.center)) heq) ▸ hbr⟩

theorem rationalActualWideActions_mono {nx ny M : ℕ}
    (parent : TargetInterval nx) (complete nearby : List (ℕ × TargetInterval ny)) (P : ℕ)
    (hsubset : ∀ br ∈ nearby, br ∈ complete) :
    ∀ action ∈ rationalActualWideActions (M := M) parent nearby P,
      action ∈ rationalActualWideActions parent complete P := by
  intro action ha
  obtain ⟨br, hbr, ha⟩ := List.mem_flatMap.mp ha
  exact List.mem_flatMap.mpr ⟨br, hsubset br hbr, ha⟩

theorem localRefinementRepresentatives_complete {n N P F b : ℕ} {a : ℚ}
    (initial : TargetInterval n → ℚ) (q r : TargetInterval n)
    (hw : 0 < initial q) (ha : 1 ≤ a) (hF : 1 ≤ F)
    (hspatial : |initial q - initial r| ≤ 32 * F * targetEndpointDistance q r)
    (hrep : (b, r) ∈ representativeList N P F a initial)
    (hcompetitive : 128 * (F : ℚ) * targetEndpointDistance q r ≤ initial q) :
    (b, r) ∈ localRefinementRepresentatives N P F a initial q := by
  have hconditions := representativeList_conditions a initial hrep
  have hnumeric := refinement_cone_locality_numeric hw ha (show (1 : ℚ) ≤ F by exact_mod_cast hF)
    (Nat.cast_nonneg (α := ℚ) (targetEndpointDistance q r)) hspatial hconditions.2.2.2
    le_rfl hcompetitive
  have hdist : targetEndpointDistance q r ≤ ⌈initial q⌉₊ := by
    have hceil : initial q ≤ (⌈initial q⌉₊ : ℚ) := Nat.le_ceil _
    exact_mod_cast hnumeric.2.2.trans hceil
  apply List.mem_flatMap.mpr
  refine ⟨b, List.mem_filter.mpr ⟨hconditions.1, decide_eq_true ⟨hnumeric.1, hnumeric.2.1⟩⟩, ?_⟩
  apply List.mem_map.mpr
  refine ⟨r, List.mem_filter.mpr ⟨?_, decide_eq_true hconditions.2.2.2⟩, rfl⟩
  apply localTargetStates_complete (by unfold seedGridSpacing; omega) q r
    (by unfold targetEndpointDistance at hdist; omega)
    (by unfold targetEndpointDistance at hdist; omega)
    ⟨hconditions.2.1, hconditions.2.2.1⟩

/-- Local representatives retain every cone that can improve the initial
fallback. All other complete cones are discarded by their distance charge. -/
theorem localRefinementBellman_eq {nx ny M : ℕ}
    (parent : TargetInterval nx) (N P F : ℕ) (a : ℚ)
    (initial : TargetInterval ny → ℚ) (child : Fin M × TargetInterval ny → ℚ)
    (q : TargetInterval ny) (ha : 1 ≤ a) (hF : 1 ≤ F)
    (hinitial : 0 ≤ initial q) (hchild : ∀ s, 0 ≤ child s)
    (hspatial : ∀ r, |initial q - initial r| ≤ 32 * F * targetEndpointDistance q r) :
    rationalBellman initial (fun q r => targetEndpointDistance q r) (128 * F)
        (rationalActualWideActions parent (localRefinementRepresentatives N P F a initial q) P) child q =
      rationalBellman initial (fun q r => targetEndpointDistance q r) (128 * F)
        (rationalActualWideActions parent (representativeList N P F a initial) P) child q := by
  let complete := rationalActualWideActions (M := M) parent (representativeList N P F a initial) P
  let nearby := rationalActualWideActions (M := M) parent (localRefinementRepresentatives N P F a initial q) P
  let value := rationalActionValue (M := M) (fun q r : TargetInterval ny => (targetEndpointDistance q r : ℚ))
    (128 * F) child q
  have hsubset : ∀ action ∈ nearby, action ∈ complete := rationalActualWideActions_mono parent _ _ P
    (localRefinementRepresentatives_subset N P F a initial q)
  have hnonneg : ∀ action ∈ complete, 0 ≤ value action := by
    intro action ha'
    exact rationalActionValue_pruned_lower _ _ child q action 0 (by positivity)
      (rationalActualWideActions_connection_nonneg parent _ P action ha') (fun _ => hchild _)
  change rationalMinimum (initial q) (nearby.map value) = rationalMinimum (initial q) (complete.map value)
  by_cases hw : 0 < initial q
  · apply rationalMinimum_local_complete complete nearby value (initial q) hsubset
    intro action hacomplete hvalue
    obtain ⟨br, hbr, haction⟩ := List.mem_flatMap.mp hacomplete
    obtain ⟨states, hstates, heq⟩ := List.mem_map.mp haction
    have hcenter : br.2 = action.center := congrArg RationalBellmanAction.center heq
    have hcharge : 128 * (F : ℚ) * targetEndpointDistance q action.center ≤ value action := by
      exact rationalActionValue_pruned_lower _ _ child q action _ le_rfl
        (rationalActualWideActions_connection_nonneg parent _ P action hacomplete) (fun _ => hchild _)
    have hrep := localRefinementRepresentatives_complete initial q action.center hw ha hF
      (hspatial action.center) (by simpa only [← hcenter] using hbr) (hcharge.trans hvalue)
    exact List.mem_flatMap.mpr ⟨br, by simpa only [← hcenter] using hrep,
      List.mem_map.mpr ⟨states, hstates, heq⟩⟩
  · have hzero : initial q = 0 := le_antisymm (le_of_not_gt hw) hinitial
    have hmin (indices : List (RationalBellmanAction (TargetInterval ny) (Fin M × TargetInterval ny) M))
        (hindices : ∀ action ∈ indices, action ∈ complete) : rationalMinimum (initial q) (indices.map value) = 0 := by
      apply le_antisymm
      · exact (rationalMinimum_le_fallback _ _).trans_eq hzero
      · apply (le_rationalMinimum_iff _ _ _).2
        refine ⟨hinitial, ?_⟩
        intro v hv
        obtain ⟨action, haction, rfl⟩ := List.mem_map.mp hv
        exact hnonneg action (hindices action haction)
    exact (hmin nearby hsubset).trans (hmin complete (fun _ h => h)).symm

/-- The actual initial table supplies the spatial hypotheses on a good
seed. Thus the bounded local search computes its literal warmup cone. -/
theorem physical_localRefinementBellman_eq {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (hsize : source.length + target.length ≤ N)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (node : PhysicalNode M J) (child : Fin M × TargetInterval target.length → ℚ)
    (hchild : ∀ s, 0 ≤ child s) (q : TargetInterval target.length) :
    rationalBellman (fun r => stageInitial source target U N P F A (node, r))
        (fun q r => targetEndpointDistance q r) (128 * F)
        (rationalActualWideActions (physicalSourceInterval source.length node)
          (localRefinementRepresentatives N P F (refinementFactor A F)
            (fun r => stageInitial source target U N P F A (node, r)) q) P) child q =
      rationalBellman (fun r => stageInitial source target U N P F A (node, r))
        (fun q r => targetEndpointDistance q r) (128 * F)
        (rationalActualWideActions (physicalSourceInterval source.length node)
          (stageRepresentatives source target U N P F A node) P) child q := by
  have hfactor := refinementFactor_spec A F (by omega : 0 < F)
  unfold stageRepresentatives
  apply localRefinementBellman_eq (M := M) (physicalSourceInterval source.length node)
    N P F (refinementFactor A F) (fun r => stageInitial source target U N P F A (node, r)) child q hfactor.1 hF
    (stageInitial_nonneg_all_seeds source target U N P F A (node, q)) hchild
  intro r
  have hqr := physicalInitialTable_spatial source target U N P F A (refinementFactor A F)
    hsize hP hF hA hfactor.1 hfactor.2 hseed node q r
  have hrq := physicalInitialTable_spatial source target U N P F A (refinementFactor A F)
    hsize hP hF hA hfactor.1 hfactor.2 hseed node r q
  have hsym : targetEndpointDistance r q = targetEndpointDistance q r := by
    exact congrArg₂ (· + ·) (Nat.dist_comm _ _) (Nat.dist_comm _ _)
  rw [hsym] at hrq
  apply abs_le.mpr
  constructor <;> dsimp only [stageInitial] <;> linarith only [hqr, hrq]

end EditApproximation

end OAI
