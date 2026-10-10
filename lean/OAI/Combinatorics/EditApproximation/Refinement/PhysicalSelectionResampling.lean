import OAI.Combinatorics.EditApproximation.Refinement.PhysicalSelectionProgram
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRefinementLocality

namespace OAI

/-! Literal parent-coordinate replacement in the finite selection program. -/

namespace EditApproximation

section Resampling

variable {α : Type*} [DecidableEq α] {M J R : ℕ}
  (source target : List α) (U : PhysicalEntry M J target.length → ℕ)
  (N P F : ℕ) (A : ℚ) (T thetaExponent H Q : ℕ) (tau η κ : ℚ)

local notation "Online" => PhysicalOnlineStreams source target U N P F A T thetaExponent H tau R
local notation "Groups" => PhysicalGroupStreams source target U N P F A thetaExponent Q R
local notation "program" => physicalProgramSelections source target U N P F A T thetaExponent H Q tau η κ

/-- Replacing exactly one parent's arrays leaves every other raw parent
selection function unchanged. The replacement arrays retain their literal
finite coordinate types. -/
noncomputable def physicalProgramResampleOnline (stream : Online) (node : PhysicalInternalNode M J)
    (fresh : ∀ representative : Fin (stageRepresentatives source target U N P F A node.1).length,
      Fin R → Fin (optimizerTriangularMass
        (physicalProgramBandK source target U N P F A T thetaExponent H tau node representative))) : Online := by
  classical
  exact Function.update stream node fresh

noncomputable def physicalProgramResampleGroups (stream : Groups) (node : PhysicalInternalNode M J)
    (fresh : ∀ scale : Fin (dyadicScales N).length,
      ∀ _cell : Fin (physicalProgramCells source target U N P F A thetaExponent node.1
        ((dyadicScales N).get scale)).length,
        Fin R → ∀ h : Fin (groupDyadicScales M ((dyadicScales N).get scale) F).length,
          Fin (groupSampleCount M Q ((dyadicScales N).get scale)
            (groupDyadicScaleAt M ((dyadicScales N).get scale) F h)) → Fin M) : Groups := by
  classical
  exact Function.update stream node fresh

theorem physicalProgramResampleOnline_same (stream : Online) (node : PhysicalInternalNode M J)
    (fresh) : physicalProgramResampleOnline source target U N P F A T thetaExponent H tau stream node fresh node = fresh := by
  classical
  exact Function.update_self node fresh stream

theorem physicalProgramResampleGroups_same (stream : Groups) (node : PhysicalInternalNode M J)
    (fresh) : physicalProgramResampleGroups source target U N P F A thetaExponent Q stream node fresh node = fresh := by
  classical
  exact Function.update_self node fresh stream

theorem physicalProgramResampleOnline_other (stream : Online) (node label : PhysicalInternalNode M J)
    (fresh) (hne : label ≠ node) :
    physicalProgramResampleOnline source target U N P F A T thetaExponent H tau stream node fresh label = stream label := by
  classical
  exact Function.update_of_ne hne _ _

theorem physicalProgramResampleGroups_other (stream : Groups) (node label : PhysicalInternalNode M J)
    (fresh) (hne : label ≠ node) :
    physicalProgramResampleGroups source target U N P F A thetaExponent Q stream node fresh label = stream label := by
  classical
  exact Function.update_of_ne hne _ _

variable [NeZero R]

theorem physicalProgramSelections_online_congr_at (online first : Online) (groups : Groups)
    (node : PhysicalNode M J)
    (hlocal : ∀ hbelow : node.1.val < J, online ⟨node, hbelow⟩ = first ⟨node, hbelow⟩) :
    (program online groups).online node = (program first groups).online node := by
  funext children t q
  dsimp only [physicalProgramSelections]
  unfold physicalProgramOnline
  split_ifs with hbelow
  · rw [hlocal hbelow]
  · rfl

theorem physicalProgramSelections_groups_congr_at (online : Online) (groups first : Groups)
    (node : PhysicalNode M J)
    (hlocal : ∀ hbelow : node.1.val < J, groups ⟨node, hbelow⟩ = first ⟨node, hbelow⟩) :
    (program online groups).groups node = (program online first).groups node := by
  funext children t
  dsimp only [physicalProgramSelections]
  unfold physicalProgramGroups
  split_ifs with hbelow
  · rw [hlocal hbelow]
  · rfl

theorem physicalProgramResample_deeper (online : Online) (groups : Groups)
    (node : PhysicalInternalNode M J) (freshOnline) (freshGroups)
    (label : PhysicalNode M J) (hdeeper : node.1.1.val < label.1.val) :
    let nextOnline := physicalProgramResampleOnline source target U N P F A T thetaExponent H tau online node freshOnline
    let nextGroups := physicalProgramResampleGroups source target U N P F A thetaExponent Q groups node freshGroups
    (program nextOnline nextGroups).groups label = (program online groups).groups label ∧
      (program nextOnline nextGroups).online label = (program online groups).online label := by
  have hne (hbelow : label.1.val < J) : (⟨label, hbelow⟩ : PhysicalInternalNode M J) ≠ node := by
    intro heq
    have hdepth := congrArg (fun n : PhysicalInternalNode M J => n.1.1.val) heq
    change label.1.val = node.1.1.val at hdepth
    omega
  dsimp only
  constructor
  · exact physicalProgramSelections_groups_congr_at source target U N P F A T thetaExponent H Q tau η κ
      online (physicalProgramResampleGroups source target U N P F A thetaExponent Q groups node freshGroups)
      groups label (fun hbelow => physicalProgramResampleGroups_other source target U N P F A thetaExponent Q
        groups node ⟨label, hbelow⟩ freshGroups (hne hbelow))
  · exact physicalProgramSelections_online_congr_at source target U N P F A T thetaExponent H Q tau η κ
      (physicalProgramResampleOnline source target U N P F A T thetaExponent H tau online node freshOnline)
      online groups label (fun hbelow => physicalProgramResampleOnline_other source target U N P F A T thetaExponent H tau
        online node ⟨label, hbelow⟩ freshOnline (hne hbelow))

/-- Literal query-filtered selections contain the accepted physical sampler
using the same complete child history. -/
theorem physicalProgram_online_action_mem (online : Online) (groups : Groups) (delta : ℚ)
    (node : PhysicalInternalNode M J)
    (representative : Fin (stageRepresentatives source target U N P F A node.1).length) (b : ℕ)
    (member : UnskippedBand source target (physicalSourceInterval source.length node.1)
      b P thetaExponent tau F
      (physicalBandChildMassTable source target U N P F A T node.1 node.2)
      (physicalBandChildInitial source target U N P F A node.1 node.2))
    (hget : (stageRepresentatives source target U N P F A node.1).get representative = (b, member.center))
    (t : ℕ) (q : TargetInterval target.length)
    (hquery : physicalProgramOnlineGuard source target U N P F A node.1 q (b, member.center)) :
    sharedBandRationalAction member.center
      (physicalBandOnlineDraw source target U N P F A T delta (program online groups) node.1 node.2
        b thetaExponent tau member.center member.nonempty η κ
        (physicalProgramBandG source target U N P F A T thetaExponent H tau node representative)
        (physicalProgramBandK source target U N P F A T thetaExponent H tau node representative) t
        (online node representative (Fin.ofNat R t))) ∈
      physicalNodeOnline source target U N P F A T delta (program online groups) node.1 node.2 t q := by
  exact physicalProgramOnline_contains_accepted source target U N P F A T thetaExponent H tau η κ
    online node representative b member hget
    (physicalNodeChildren source target U N P F A T delta (program online groups) node.1 node.2) t q hquery

theorem physicalProgram_group_action_mem (online : Online) (groups : Groups) (delta : ℚ)
    (node : PhysicalInternalNode M J) (scale : Fin (dyadicScales N).length)
    (cell : Fin (physicalProgramCells source target U N P F A thetaExponent node.1
      ((dyadicScales N).get scale)).length)
    (hnonempty : physicalNodeCellBands source target U N P F A T node.1 node.2
      ((dyadicScales N).get scale) thetaExponent tau
      ((physicalProgramCells source target U N P F A thetaExponent node.1
        ((dyadicScales N).get scale)).get cell) ≠ []) (t : ℕ) :
    (physicalNodeSelectedGroup source target U N P F A T delta (program online groups) node.1 node.2
      ((dyadicScales N).get scale) thetaExponent Q tau
      ((physicalProgramCells source target U N P F A thetaExponent node.1
        ((dyadicScales N).get scale)).get cell) hnonempty t
      (groups node scale cell (Fin.ofNat R t))).rationalAction ∈
      physicalNodeGroups source target U N P F A T delta (program online groups) node.1 node.2 t := by
  exact physicalProgramGroups_contains_selected source target U N P F A T thetaExponent Q tau groups
    node scale cell hnonempty
    (physicalNodeChildren source target U N P F A T delta (program online groups) node.1 node.2) t


end Resampling

end EditApproximation

end OAI
