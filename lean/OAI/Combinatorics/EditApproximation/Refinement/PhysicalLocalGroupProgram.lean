import OAI.Combinatorics.EditApproximation.Geometry.LocalGroupCones
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalSelectionProgram

namespace OAI

/-! The finite indexed group program has an equivalent cell-keyed
realization. Good initial seeds permit its whole cone to be evaluated
using only the directly enumerated query cells. -/

namespace EditApproximation

section Program

variable {α : Type*} [DecidableEq α] {M J : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F exponent Q : ℕ) (A : ℚ)

def physicalGroupStreamsOfKeys {R : ℕ}
    (draw : PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q) :
    PhysicalGroupStreams source target U N P F A exponent Q R :=
  fun node scale cell time => draw node time ((dyadicScales N).get scale)
    ((physicalProgramCells source target U N P F A exponent node.1
      ((dyadicScales N).get scale)).get cell)

theorem physicalProgramCells_keyed (node : PhysicalNode M J) (b : ℕ) :
    physicalProgramCells source target U N P F A exponent node b =
      representativeCells N P F b (refinementFactor A F) ((2 : ℚ) ^ (-(exponent : ℤ)))
        (fun q => stageInitial source target U N P F A (node, q)) := rfl

theorem physicalProgramGroups_keyed (T : ℕ) (tau : ℚ) {R : ℕ} [NeZero R]
    (draw : PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
    (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (children : PhysicalChildTables M target.length) (t : ℕ) :
    physicalProgramGroups source target U N P F A T exponent Q tau
        (physicalGroupStreamsOfKeys source target U N P F exponent Q A draw) node children t =
      completeCellGroupActions source target (physicalSourceInterval source.length node)
        N P F exponent Q tau (refinementFactor A F)
        (fun q => stageInitial source target U N P F A (node, q))
        (physicalBandChildMassTable source target U N P F A T node hbelow)
        (physicalBandChildInitial source target U N P F A node hbelow)
        (fun i q => children i t q) (draw ⟨node, hbelow⟩ (Fin.ofNat R (t - 1))) := by
  unfold physicalProgramGroups
  rw [dite_eq_left hbelow]
  unfold completeCellGroupActions
  conv_rhs => rw [← List.map_get_finRange (dyadicScales N)]
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro scale _
  rw [← physicalProgramCells_keyed source target U N P F exponent A node]
  conv_rhs => rw [← List.map_get_finRange (physicalProgramCells source target U N P F A exponent node
    ((dyadicScales N).get scale))]
  simp only [List.filterMap_map, Function.comp_def, physicalGroupStreamsOfKeys]

/-- Actual chosen-group cone at one node, evaluated by bounded query
cell loops. The old-child fallback is arbitrary provided it is at most
the literal initial value. -/
theorem physicalProgramGroups_local_minimum (T : ℕ) (tau : ℚ) {R : ℕ} [NeZero R]
    (draw : PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
    (node : PhysicalNode M J) (hbelow : node.1.val < J)
    (children : PhysicalChildTables M target.length) (t : ℕ)
    (q : TargetInterval target.length) (fallback : ℚ)
    (hsize : source.length + target.length ≤ N) (hP : 66 ≤ P) (hF : 1 ≤ F) (hA : 1 ≤ A)
    (hseed : ∀ state, stateEditCost (physicalSource source state.1) target state.2 ≤ U state ∧
      (U state : ℚ) ≤ A * stateEditCost (physicalSource source state.1) target state.2)
    (hfallback : fallback ≤ stageInitial source target U N P F A (node, q))
    (hchild : ∀ i r, 0 ≤ children i t r) :
    rationalMinimum fallback
        ((localCellGroupActions source target (physicalSourceInterval source.length node)
          N P F exponent Q tau (refinementFactor A F)
          (fun r => stageInitial source target U N P F A (node, r))
          (physicalBandChildMassTable source target U N P F A T node hbelow)
          (physicalBandChildInitial source target U N P F A node hbelow)
          (fun i r => children i t r) (draw ⟨node, hbelow⟩ (Fin.ofNat R (t - 1))) q).map
          (rationalActionValue (fun q r => targetEndpointDistance q r) (128 * F)
            (fun is => children is.1 t is.2) q)) =
      rationalMinimum fallback
        ((physicalProgramGroups source target U N P F A T exponent Q tau
          (physicalGroupStreamsOfKeys source target U N P F exponent Q A draw) node children t).map
          (rationalActionValue (fun q r => targetEndpointDistance q r) (128 * F)
            (fun is => children is.1 t is.2) q)) := by
  rw [physicalProgramGroups_keyed source target U N P F exponent Q A T tau draw node hbelow children t]
  have hfactor := refinementFactor_spec A F (by omega : 0 < F)
  have hspatial : ∀ r, |stageInitial source target U N P F A (node, q) -
      stageInitial source target U N P F A (node, r)| ≤ 32 * F * targetEndpointDistance q r := by
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
  exact localCellGroupMinimum_eq source target (physicalSourceInterval source.length node)
    N P F exponent Q tau (refinementFactor A F)
    (fun r => stageInitial source target U N P F A (node, r))
    (physicalBandChildMassTable source target U N P F A T node hbelow)
    (physicalBandChildInitial source target U N P F A node hbelow)
    (fun i r => children i t r) (draw ⟨node, hbelow⟩ (Fin.ofNat R (t - 1))) q fallback
    hfactor.1 hF hfallback hchild hspatial

end Program

end EditApproximation

end OAI
