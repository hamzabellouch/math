import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarActionOrder

namespace OAI

/-! The eight pulses belonging to one branch occur in strict chronological
order inside the actual finite instruction list. -/

namespace ForcedComputation.Recorder.Planar

open ShearFlows

def ownPhase : Fin 8 → Phase :=
  letI := ShearFlows.neZeroFour
  ![.extractHorizontal, .extractVertical, .scale 0, .scale 1,
    .scale 2, .scale 3, .insertVertical, .insertHorizontal]

def branchIndices (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) : Fin 8 → Fin (actions M hM).length :=
  ![extractionIndex M hM b 0, extractionIndex M hM b 1,
    scalingIndex M hM b 0, scalingIndex M hM b 1,
    scalingIndex M hM b 2, scalingIndex M hM b 3,
    insertionIndex M hM b 0, insertionIndex M hM b 1]

theorem branchIndices_get (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) (k : Fin 8) :
    (actions M hM).get (branchIndices M hM b k) = ⟨b, ownPhase k⟩ := by
  fin_cases k
  · exact extractionIndex_get M hM b 0
  · exact extractionIndex_get M hM b 1
  · exact scalingIndex_get M hM b 0
  · exact scalingIndex_get M hM b 1
  · exact scalingIndex_get M hM b 2
  · exact scalingIndex_get M hM b 3
  · exact insertionIndex_get M hM b 0
  · exact insertionIndex_get M hM b 1

theorem branchIndices_values (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) :
    (fun k => (branchIndices M hM b k).val) =
      ![2 * (sourceRank M hM b).val, 2 * (sourceRank M hM b).val + 1,
        2 * (geometricBranches M hM).length + 4 * (branchIndex M hM b).val,
        2 * (geometricBranches M hM).length + 4 * (branchIndex M hM b).val + 1,
        2 * (geometricBranches M hM).length + 4 * (branchIndex M hM b).val + 2,
        2 * (geometricBranches M hM).length + 4 * (branchIndex M hM b).val + 3,
        6 * (geometricBranches M hM).length + 2 * (targetRank M hM b).val,
        6 * (geometricBranches M hM).length + 2 * (targetRank M hM b).val + 1] := by
  funext k
  fin_cases k <;> rfl

theorem ordered_indices_strictMono (n s b t : ℕ) (hs : s < n) (hb : b < n) :
    StrictMono (![2 * s, 2 * s + 1, 2 * n + 4 * b, 2 * n + 4 * b + 1,
      2 * n + 4 * b + 2, 2 * n + 4 * b + 3, 6 * n + 2 * t, 6 * n + 2 * t + 1] : Fin 8 → ℕ) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro k
  fin_cases k
  · change 2 * s < 2 * s + 1
    omega
  · change 2 * s + 1 < 2 * n + 4 * b
    omega
  · change 2 * n + 4 * b < 2 * n + 4 * b + 1
    omega
  · change 2 * n + 4 * b + 1 < 2 * n + 4 * b + 2
    omega
  · change 2 * n + 4 * b + 2 < 2 * n + 4 * b + 3
    omega
  · change 2 * n + 4 * b + 3 < 6 * n + 2 * t
    omega
  · change 6 * n + 2 * t < 6 * n + 2 * t + 1
    omega

theorem branchIndices_strictMono (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) : StrictMono (branchIndices M hM b) := by
  have hs := (sourceRank M hM b).isLt
  have hsl := (sourceOrder_perm M hM).length_eq
  have hnat : StrictMono (fun k => (branchIndices M hM b k).val) := by
    rw [branchIndices_values]
    exact ordered_indices_strictMono _ _ _ _ (by omega) (branchIndex M hM b).isLt
  exact hnat

end ForcedComputation.Recorder.Planar

end OAI
