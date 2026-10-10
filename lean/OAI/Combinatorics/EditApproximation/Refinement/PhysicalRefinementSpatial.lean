import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRefinementInvariants
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalSpatial
import OAI.Combinatorics.EditApproximation.Numerics.RationalWideSpatial

namespace OAI

/-! Nonnegativity, exact zero states and spatial regularity of the full stage. -/

namespace EditApproximation

theorem stageInitial_spatial {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (hsize : source.length + target.length ≤ N)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (node : PhysicalNode M J) (q q' : TargetInterval target.length) :
    stageInitial source target U N P F A (node, q) ≤
      stageInitial source target U N P F A (node, q') + (128 * F : ℚ) * targetEndpointDistance q q' := by
  have hfactor := refinementFactor_spec A F (by omega)
  have h32 := physicalInitialTable_spatial source target U N P F A (refinementFactor A F)
    hsize hP hF hA hfactor.1 hfactor.2 hseed node q q'
  have hcharge : (32 * F : ℚ) * targetEndpointDistance q q' ≤
      (128 * F : ℚ) * targetEndpointDistance q q' := by
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    exact mul_le_mul_of_nonneg_right (by norm_num : (32 : ℚ) ≤ 128) (Nat.cast_nonneg F)
  change physicalInitialTable source target U N P F A (refinementFactor A F) (node, q) ≤
    physicalInitialTable source target U N P F A (refinementFactor A F) (node, q') +
      (128 * F : ℚ) * targetEndpointDistance q q'
  exact le_trans h32 (add_le_add_right hcharge
    (physicalInitialTable source target U N P F A (refinementFactor A F) (node, q')))

theorem physicalRefinement_nonneg {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (hM : 0 < M) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (hsize : source.length + target.length ≤ N)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (T : ℕ) (hT : 0 < T) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A)) (node : PhysicalNode M J)
    (t : ℕ) (q : TargetInterval target.length) :
    0 ≤ physicalRefinement source target U N P F A T delta choices node t q := by
  have h := (physicalRefinement_stage_bounds source target hM U N P F A hsize hP hF hA hseed
    T hT delta choices node t q).1
  have hzero : 0 ≤ physicalLower source target (refinementFactor A F : ℝ) (node, q) :=
    (abs_nonneg _).trans (le_max_right _ _)
  exact (Rat.cast_nonneg (K := ℝ)).mp (hzero.trans h)

theorem physicalRefinement_zero_cost {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (hM : 0 < M) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (hsize : source.length + target.length ≤ N)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (T : ℕ) (hT : 0 < T) (delta : ℚ)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A)) (node : PhysicalNode M J)
    (t : ℕ) (q : TargetInterval target.length)
    (hcost : stateEditCost (physicalSource source node) target q = 0) :
    physicalRefinement source target U N P F A T delta choices node t q = 0 := by
  have hb := physicalRefinement_stage_bounds source target hM U N P F A hsize hP hF hA hseed
    T hT delta choices node t q
  have hu := hb.2.1.trans (hb.2.2.1.trans (hb.2.2.2.1.trans hb.2.2.2.2))
  rw [hcost] at hu
  simp only [Nat.cast_zero, mul_zero] at hu
  exact le_antisymm hu (physicalRefinement_nonneg source target hM U N P F A hsize hP hF hA hseed
    T hT delta choices node t q)

theorem physicalRefinement_spatial {α : Type*} [DecidableEq α] {M J : ℕ}
    (source target : List α) (hM : 0 < M) (U : PhysicalEntry M J target.length → ℕ)
    (N P F : ℕ) (A : ℚ) (hsize : source.length + target.length ≤ N)
    (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (T : ℕ) (hT : 0 < T) (delta : ℚ) (hdelta : 0 ≤ delta)
    (choices : PhysicalSelections M J source.length target.length P
      (stageRepresentatives source target U N P F A)) (node : PhysicalNode M J)
    (t : ℕ) (q q' : TargetInterval target.length) :
    physicalRefinement source target U N P F A T delta choices node t q ≤
      (1 + delta) * physicalRefinement source target U N P F A T delta choices node t q' +
        (128 * F : ℚ) * targetEndpointDistance q q' := by
  have hL : (0 : ℚ) ≤ 128 * F := mul_nonneg (by norm_num) (Nat.cast_nonneg _)
  have hinit (node : PhysicalNode M J) (r r' : TargetInterval target.length) :
      stageInitial source target U N P F A (node, r) ≤
        stageInitial source target U N P F A (node, r') + (128 * F : ℚ) * targetEndpointDistance r r' := by
    exact stageInitial_spatial source target U N P F A hsize hP hF hA hseed node r r'
  have hnonneg := physicalRefinement_nonneg source target hM U N P F A hsize hP hF hA hseed
    T hT delta choices node t q'
  have hmul := mul_nonneg hdelta hnonneg
  by_cases hbelow : node.1.val < J
  · by_cases hleaf : (physicalSourceInterval source.length node).hi -
        (physicalSourceInterval source.length node).lo ≤ 1
    · rw [physicalRefinement_at_terminal _ _ _ _ _ _ _ _ _ _ node (Or.inr hleaf)] at hmul ⊢
      rw [physicalRefinement_at_terminal _ _ _ _ _ _ _ _ _ _ node (Or.inr hleaf)]
      nlinarith only [hinit node q q', hmul]
    · cases t with
      | zero =>
        rw [physicalRefinement_zero] at hmul ⊢
        rw [physicalRefinement_zero]
        have hinitR (n : PhysicalNode M J) (r r' : TargetInterval target.length) :
            (stageInitial source target U N P F A (n, r) : ℝ) ≤
              (stageInitial source target U N P F A (n, r') : ℝ) +
                ((128 * F : ℚ) : ℝ) * targetEndpointDistance r r' := by
          exact_mod_cast hinit n r r'
        have hw := physicalWarmup_spatial source target P ((128 * F : ℚ) : ℝ)
          ((Rat.cast_nonneg (K := ℝ)).mpr hL)
          (fun s => (stageInitial source target U N P F A s : ℝ))
          (stageRepresentatives source target U N P F A) hinitR T node q q'
        have hwQ : stageWarmup source target U N P F A T (node, q) ≤
            stageWarmup source target U N P F A T (node, q') +
              (128 * F : ℚ) * targetEndpointDistance q q' := by
          apply (Rat.cast_le (K := ℝ)).mp
          simpa only [stageWarmup, rationalPhysicalWarmup_cast, Rat.cast_add, Rat.cast_mul,
            Rat.cast_natCast] using hw
        nlinarith only [hwQ, hmul]
      | succ t =>
        let children : PhysicalChildTables M target.length := fun i =>
          physicalRefinement source target U N P F A T delta choices (physicalChild node hbelow i)
        have hcone : 0 ≤ rationalWideStepCone (physicalSourceInterval source.length node)
            (stageRepresentatives source target U N P F A node) P
            (fun r => stageInitial source target U N P F A (node, r)) (128 * F)
            (fun is => children is.1 t is.2) (fun is => children is.1 (t + 1) is.2)
            (choices.groups node children (t + 1)) q' := by
          rw [physicalRefinement_succ _ _ _ _ _ _ _ _ _ _ node hbelow hleaf] at hnonneg
          exact hnonneg.trans (rationalRefinementUpdate_le_cone _ _ _)
        rw [physicalRefinement_succ _ _ _ _ _ _ _ _ _ _ node hbelow hleaf,
          physicalRefinement_succ _ _ _ _ _ _ _ _ _ _ node hbelow hleaf]
        exact rationalWideStep_spatial _ _ P _ (128 * F) delta hL hdelta _ _ _
          (choices.online node children (t + 1)) q q' (hinit node q q') hcone
  · rw [physicalRefinement_at_terminal _ _ _ _ _ _ _ _ _ _ node (Or.inl hbelow)] at hmul ⊢
    rw [physicalRefinement_at_terminal _ _ _ _ _ _ _ _ _ _ node (Or.inl hbelow)]
    nlinarith only [hinit node q q', hmul]

end EditApproximation

end OAI
