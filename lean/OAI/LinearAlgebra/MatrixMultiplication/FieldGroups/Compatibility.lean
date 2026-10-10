import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.NativeLaws

namespace OAI

/-! Group assignments, orbit counts and extraction capacities. -/

noncomputable section

namespace MatrixMultiplication.AllFieldGroupCompatibility

open AllFieldHistory AllFieldHistoryChildLaws AllFieldHistoryGroupMasks
open AllFieldHistoryGroupedRecovery AllFieldGroupOrbitData
open JointPopulation JointCanonicalization

attribute [local instance] Classical.propDecidable

variable {K tick : ℕ}

theorem groupIdealSide_ownWord (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma)
    (hw : groupIdealSide allocation m ε (sigma side) sigma e w) :
    tripleSide side (AllFieldGroupOrbitData.coarse allocation m sigma e) =
      ownWord allocation m sigma w := by
  change tripleSide side
    (reorder sigma (triple (Counts (K := K) (tick := tick) allocation m sigma) e)) = _
  rw [tripleSide_reorder]
  funext p
  have hs : tripleSide (sigma side)
      (triple (Counts (K := K) (tick := tick) allocation m sigma) e) p =
      shapeSide (sigma side) ((e p.1).val p.2) := by
    generalize sigma side = s
    fin_cases s <;> rfl
  rw [hs]
  exact (hw.1 p.1 p.2).symm

theorem groupIdealSide_fineCompatible (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma)
    (hw : groupIdealSide allocation m ε (sigma side) sigma e w) :
    fineCompatible allocation m ε sigma side e w := by
  intro right h u hd
  apply JointPopulationCompatibility.shape_count_window_of_typeWindow
    (Counts (K := K) (tick := tick) allocation m sigma) e h u
    (fun i => statistic h.val (if right then (w h i).2 else (w h i).1))
    (compatibilityLaw right side sigma h u) (AllFieldHistoryMasks.childWidth ε h.val)
  intro hu
  rw [AllFieldGroupNativeLaws.compatibilityLaw_eq allocation m sigma right side h u hu hd]
  cases right
  · exact (hw.2 h u hu).1
  · exact (hw.2 h u hu).2

theorem groupIdealSide_compatible (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma)
    (hw : groupIdealSide allocation m ε (sigma side) sigma e w) :
    Compatible allocation m ε sigma side e w :=
  ⟨groupIdealSide_ownWord allocation m ε sigma side e w hw,
    groupIdealSide_fineCompatible allocation m ε sigma side e w hw⟩

theorem admissible_compatible (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma)
    (hw : Admissible allocation m ε sigma side e w) :
    Compatible allocation m ε sigma side e w :=
  groupIdealSide_compatible allocation m ε sigma side e w hw.1

end MatrixMultiplication.AllFieldGroupCompatibility

end

end OAI
