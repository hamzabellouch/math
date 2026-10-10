import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarProgramBounds

namespace OAI

/-! Clearance for the actual extraction and insertion tubes, with the
computed common collar. These inequalities are independent of tape codes. -/

namespace ForcedComputation.PlanarRouting

open ShearFlows

theorem recenter_recenter (R : RationalBox 2) (p : Fin 2 → ℚ) :
    recenter (recenter R p) (centerQ R) = R := by
  apply box_ext
  · funext j
    change centerQ R j - halfWidthQ (recenter R p) j = R.lower j
    rw [recenter_halfWidthQ, centerQ_sub_halfWidthQ]
  · funext j
    change centerQ R j + halfWidthQ (recenter R p) j = R.upper j
    rw [recenter_halfWidthQ, centerQ_add_halfWidthQ]

theorem translationTube_reverse (R : RationalBox 2) (p : Fin 2 → ℚ) :
    translationTube (recenter R p) (centerQ R) = translationTube R p := by
  unfold translationTube
  rw [recenter_recenter]
  apply box_ext <;> funext j
  · exact min_comm _ _
  · exact max_comm _ _

theorem horizontalTube_upper (R : RationalBox 2) (x : ℚ) :
    (translationTube R (horizontalCenter R x)).upper 1 = R.upper 1 := by
  change max (R.upper 1) (centerQ R 1 + halfWidthQ R 1) = R.upper 1
  rw [centerQ_add_halfWidthQ, max_self]

theorem low_tube_parking_gap {n : ℕ} {κ : ℚ} (hκ : κ ≤ 1 / 64)
    (R : RationalBox 2) (x : ℚ) (hR : R.upper 1 ≤ 1 / 3) (i : Fin n) :
    EndpointGap (1 / 4) (translationTube R (horizontalCenter R x)) (parkingBox n κ i) := by
  refine ⟨1, Or.inl ?_⟩
  rw [horizontalTube_upper]
  change R.upper 1 + 1 / 4 ≤ 3 / 4 - (3 / 8) * κ
  linarith

end ForcedComputation.PlanarRouting

namespace ForcedComputation.Recorder.Planar

open ShearFlows PlanarRouting PlanarHamiltonian

theorem branchIndex_injective (M : Alternating.Machine) (hM : M.WellFormed) :
    Function.Injective (branchIndex M hM) := by
  intro b c he
  have h := congrArg (branchAt M hM) he
  simpa only [branchAt_index] using h

theorem source_branch_gap (M : Alternating.Machine) (hM : M.WellFormed)
    {b c : Branch (finiteMachine M hM)} (hne : b ≠ c) :
    16 * routingCollar M hM ≤ boxGap (instruction M hM b).source (instruction M hM c).source := by
  have hi := routingCollar_source_gap M hM
    (show branchIndex M hM b ≠ branchIndex M hM c from fun h => hne (branchIndex_injective M hM h))
  simpa only [sourceFamily, branchAt_index] using hi

theorem target_branch_gap (M : Alternating.Machine) (hM : M.WellFormed)
    {b c : Branch (finiteMachine M hM)} (hne : b ≠ c) :
    16 * routingCollar M hM ≤ boxGap (instruction M hM b).target (instruction M hM c).target := by
  have hi := routingCollar_target_gap M hM
    (show branchIndex M hM b ≠ branchIndex M hM c from fun h => hne (branchIndex_injective M hM h))
  simpa only [targetFamily, branchAt_index] using hi

theorem routingCollar_small (M : Alternating.Machine) (hM : M.WellFormed) :
    2 * routingCollar M hM < 1 / 4 ∧
      2 * routingCollar M hM < 1 / 24 ∧
      2 * routingCollar M hM < parkingScale (geometricBranches M hM).length := by
  have h := routingCollar_parking_bound M hM
  have hp := parkingScale_pos (geometricBranches M hM).length
  have hu := parkingScale_le (geometricBranches M hM).length
  constructor
  · linarith
  constructor <;> linarith

theorem source_extraction_clearance (M : Alternating.Machine) (hM : M.WellFormed)
    {i j : Fin (sourceOrder M hM).length} (hij : i < j) (endpoint : ℚ)
    (hendpoint : centerQ (instruction M hM ((sourceOrder M hM).get i)).source 0 ≤ endpoint) :
    let R := (instruction M hM ((sourceOrder M hM).get i)).source
    let S := (instruction M hM ((sourceOrder M hM).get j)).source
    EndpointGap (boxGap R S) (translationTube R (horizontalCenter R endpoint)) S ∧
      2 * routingCollar M hM < boxGap R S := by
  let b := (sourceOrder M hM).get i
  let c := (sourceOrder M hM).get j
  have hne : b ≠ c := by
    intro he
    exact (ne_of_lt hij) ((List.nodup_iff_injective_get.mp (sourceOrder_nodup M hM)) he)
  have hg := sourceOrder_sweep_gap M hM hij (endpoint + halfWidthQ (instruction M hM b).source 0)
  have hsmall := source_branch_gap M hM hne
  have hδ := routingCollar_pos M hM
  constructor
  · rw [horizontalTube_eq_rightSweep _ hendpoint]
    exact hg.2
  · linarith

end ForcedComputation.Recorder.Planar

end OAI
