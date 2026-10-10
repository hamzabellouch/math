import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarClearance

namespace OAI

/-! Quantitative collar separation for the pulses that leave another branch
at rest. Horizontal sweeps avoid parking boxes; vertical sweeps stay inside
their own narrow parking columns. -/

namespace ForcedComputation.PlanarRouting

open ShearFlows

theorem verticalFrom_lower (R : RationalBox 2) (p : Fin 2 → ℚ) :
    (translationTube (recenter R (horizontalCenter R (p 0))) p).lower 0 =
      p 0 - halfWidthQ R 0 := by
  change min (p 0 - halfWidthQ R 0)
    (p 0 - halfWidthQ (recenter R (horizontalCenter R (p 0))) 0) = _
  rw [recenter_halfWidthQ, min_self]

theorem verticalFrom_upper (R : RationalBox 2) (p : Fin 2 → ℚ) :
    (translationTube (recenter R (horizontalCenter R (p 0))) p).upper 0 =
      p 0 + halfWidthQ R 0 := by
  change max (p 0 + halfWidthQ R 0)
    (p 0 + halfWidthQ (recenter R (horizontalCenter R (p 0))) 0) = _
  rw [recenter_halfWidthQ, max_self]

theorem verticalTo_lower (R : RationalBox 2) (p : Fin 2 → ℚ) :
    (translationTube (recenter R p) (horizontalCenter R (p 0))).lower 0 =
      p 0 - halfWidthQ R 0 := by
  change min (p 0 - halfWidthQ R 0) (p 0 - halfWidthQ (recenter R p) 0) = _
  rw [recenter_halfWidthQ, min_self]

theorem verticalTo_upper (R : RationalBox 2) (p : Fin 2 → ℚ) :
    (translationTube (recenter R p) (horizontalCenter R (p 0))).upper 0 =
      p 0 + halfWidthQ R 0 := by
  change max (p 0 + halfWidthQ R 0) (p 0 + halfWidthQ (recenter R p) 0) = _
  rw [recenter_halfWidthQ, max_self]

theorem column_gap_of_horizontal_bounds {n : ℕ} {κ : ℚ} (hκ : κ ≤ 1 / 64)
    {i j : Fin n} (hij : i ≠ j) {R : RationalBox 2}
    (hl : (parkingBox n κ i).lower 0 ≤ R.lower 0)
    (hu : R.upper 0 ≤ (parkingBox n κ i).upper 0) :
    EndpointGap (parkingScale n) R (parkingBox n κ j) := by
  rcases lt_or_gt_of_ne hij with h | h
  · refine ⟨0, Or.inl ?_⟩
    have hg := parkingBox_gap hκ h
    linarith
  · refine ⟨0, Or.inr ?_⟩
    exact (parkingBox_gap hκ h).trans hl

theorem verticalFrom_parking_gap {n : ℕ} {κ : ℚ} (hκ : κ ≤ 1 / 64)
    {i j : Fin n} (hij : i ≠ j) (R : RationalBox 2)
    (hw : halfWidthQ R 0 ≤ parkingScale n * κ) :
    EndpointGap (parkingScale n)
      (translationTube (recenter R (horizontalCenter R (parkingCenter n i 0)))
        (parkingCenter n i)) (parkingBox n κ j) := by
  apply column_gap_of_horizontal_bounds hκ hij
  · rw [verticalFrom_lower]
    exact sub_le_sub_left hw _
  · rw [verticalFrom_upper]
    exact add_le_add_right hw _

theorem verticalTo_parking_gap {n : ℕ} {κ : ℚ} (hκ : κ ≤ 1 / 64)
    {i j : Fin n} (hij : i ≠ j) (R : RationalBox 2)
    (hw : halfWidthQ R 0 ≤ parkingScale n * κ) :
    EndpointGap (parkingScale n)
      (translationTube (recenter R (parkingCenter n i))
        (horizontalCenter R (parkingCenter n i 0))) (parkingBox n κ j) := by
  apply column_gap_of_horizontal_bounds hκ hij
  · rw [verticalTo_lower]
    exact sub_le_sub_left hw _
  · rw [verticalTo_upper]
    exact add_le_add_right hw _

theorem verticalFrom_low_gap {n : ℕ} (i : Fin n) (R S : RationalBox 2)
    (hw : halfWidthQ R 0 ≤ 1 / 128) (hS : S.upper 0 ≤ 1 / 3) :
    EndpointGap (1 / 24)
      (translationTube (recenter R (horizontalCenter R (parkingCenter n i 0)))
        (parkingCenter n i)) S := by
  refine ⟨0, Or.inr ?_⟩
  rw [verticalFrom_lower]
  have hp := (parkingCenter_bounds n i).1
  linarith

theorem verticalTo_low_gap {n : ℕ} (i : Fin n) (R S : RationalBox 2)
    (hw : halfWidthQ R 0 ≤ 1 / 128) (hS : S.upper 0 ≤ 1 / 3) :
    EndpointGap (1 / 24)
      (translationTube (recenter R (parkingCenter n i))
        (horizontalCenter R (parkingCenter n i 0))) S := by
  refine ⟨0, Or.inr ?_⟩
  rw [verticalTo_lower]
  have hp := (parkingCenter_bounds n i).1
  linarith

end ForcedComputation.PlanarRouting

namespace ForcedComputation.Recorder.Planar

open ShearFlows PlanarRouting

theorem target_insertion_clearance (M : Alternating.Machine) (hM : M.WellFormed)
    {i j : Fin (targetOrder M hM).length} (hij : i < j) (endpoint : ℚ)
    (hendpoint : centerQ (instruction M hM ((targetOrder M hM).get j)).target 0 ≤ endpoint) :
    let R := (instruction M hM ((targetOrder M hM).get j)).target
    let S := (instruction M hM ((targetOrder M hM).get i)).target
    EndpointGap (boxGap R S) (translationTube R (horizontalCenter R endpoint)) S ∧
      2 * routingCollar M hM < boxGap R S := by
  let b := (targetOrder M hM).get j
  let c := (targetOrder M hM).get i
  have hne : b ≠ c := by
    intro he
    exact (ne_of_lt hij) ((List.nodup_iff_injective_get.mp (targetOrder_nodup M hM)) he.symm)
  have hg := targetOrder_sweep_gap M hM hij (endpoint + halfWidthQ (instruction M hM b).target 0)
  have hsmall := target_branch_gap M hM hne
  have hδ := routingCollar_pos M hM
  constructor
  · rw [horizontalTube_eq_rightSweep _ hendpoint]
    exact hg.2
  · linarith

theorem instruction_narrow_widths (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) :
    halfWidthQ (instruction M hM b).source 0 ≤
        parkingScale (geometricBranches M hM).length * bandScale M ∧
      halfWidthQ (instruction M hM b).target 0 ≤
        parkingScale (geometricBranches M hM).length * bandScale M := by
  have hw := instruction_halfWidths M hM b
  have hε : (0 : ℝ) ≤ compression M hM := by exact_mod_cast (compression_pos M hM).le
  have hκ : (0 : ℝ) ≤ bandScale M := by exact_mod_cast (bandScale_pos M).le
  constructor
  all_goals
    apply (Rat.cast_le (K := ℝ)).mp
    simp only [halfWidthQ_cast, Rat.cast_mul]
    change _ ≤ (compression M hM : ℝ) * (bandScale M : ℝ)
    nlinarith [mul_nonneg hε hκ]

def parkingRegion (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) : RationalBox 2 :=
  parkingBox (geometricBranches M hM).length (bandScale M) (branchIndex M hM b)

theorem extractHorizontal_parking_gap (M : Alternating.Machine) (hM : M.WellFormed)
    (b c : Branch (finiteMachine M hM)) :
    EndpointGap (1 / 4) (⟨b, .extractHorizontal⟩ : Action M hM).rectangle (parkingRegion M hM c) := by
  exact low_tube_parking_gap (bandScale_le M) (instruction M hM b).source _
    (((instruction_endpoint_bounds M hM b).1 1).2) (branchIndex M hM c)

theorem insertHorizontal_parking_gap (M : Alternating.Machine) (hM : M.WellFormed)
    (b c : Branch (finiteMachine M hM)) :
    EndpointGap (1 / 4) (⟨b, .insertHorizontal⟩ : Action M hM).rectangle (parkingRegion M hM c) := by
  change EndpointGap (1 / 4)
    (translationTube (recenter (instruction M hM b).target
      (horizontalCenter (instruction M hM b).target (parkingFor M hM b 0)))
      (centerQ (instruction M hM b).target)) _
  rw [translationTube_reverse]
  exact low_tube_parking_gap (bandScale_le M) (instruction M hM b).target _
    (((instruction_endpoint_bounds M hM b).2 1).2) (branchIndex M hM c)

theorem extractVertical_parking_gap (M : Alternating.Machine) (hM : M.WellFormed)
    {b c : Branch (finiteMachine M hM)} (hne : b ≠ c) :
    EndpointGap (parkingScale (geometricBranches M hM).length)
      (⟨b, .extractVertical⟩ : Action M hM).rectangle (parkingRegion M hM c) := by
  exact verticalFrom_parking_gap (bandScale_le M)
    (fun h => hne (branchIndex_injective M hM h)) (instruction M hM b).source
    (instruction_narrow_widths M hM b).1

theorem insertVertical_parking_gap (M : Alternating.Machine) (hM : M.WellFormed)
    {b c : Branch (finiteMachine M hM)} (hne : b ≠ c) :
    EndpointGap (parkingScale (geometricBranches M hM).length)
      (⟨b, .insertVertical⟩ : Action M hM).rectangle (parkingRegion M hM c) := by
  exact verticalTo_parking_gap (bandScale_le M)
    (fun h => hne (branchIndex_injective M hM h)) (instruction M hM b).target
    (instruction_narrow_widths M hM b).2

theorem scaling_parking_gap (M : Alternating.Machine) (hM : M.WellFormed)
    {b c : Branch (finiteMachine M hM)} (hne : b ≠ c) (k : Fin 4) :
    EndpointGap (parkingScale (geometricBranches M hM).length)
      (⟨b, .scale k⟩ : Action M hM).rectangle (parkingRegion M hM c) := by
  exact column_gap_of_horizontal_bounds (bandScale_le M)
    (fun h => hne (branchIndex_injective M hM h)) le_rfl le_rfl

theorem extractVertical_source_gap (M : Alternating.Machine) (hM : M.WellFormed)
    (b c : Branch (finiteMachine M hM)) :
    EndpointGap (1 / 24) (⟨b, .extractVertical⟩ : Action M hM).rectangle
      (instruction M hM c).source := by
  exact verticalFrom_low_gap (branchIndex M hM b) (instruction M hM b).source _
    ((instruction_halfWidthQ_bound M hM b).1 0) (((instruction_endpoint_bounds M hM c).1 0).2)

theorem insertVertical_target_gap (M : Alternating.Machine) (hM : M.WellFormed)
    (b c : Branch (finiteMachine M hM)) :
    EndpointGap (1 / 24) (⟨b, .insertVertical⟩ : Action M hM).rectangle
      (instruction M hM c).target := by
  exact verticalTo_low_gap (branchIndex M hM b) (instruction M hM b).target _
    ((instruction_halfWidthQ_bound M hM b).2 0) (((instruction_endpoint_bounds M hM c).2 0).2)

end ForcedComputation.Recorder.Planar

end OAI
