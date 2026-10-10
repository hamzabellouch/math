import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.AdmissibilityCore
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.GroupedRecovery

namespace OAI

/-! Group assignments, orbit counts and extraction capacities. -/

noncomputable section

namespace MatrixMultiplication.AllFieldGroupAdmissible

open AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws
open AllFieldHistoryGroupMasks AllFieldHistoryGroupedRecovery AllFieldGroupOrbitData
open JointPopulation JointCanonicalization PermutationMatching
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem used_project_admissible (F : Type*) [CommRing F]
    (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (e : AllFieldHistoryRecovery.Targets (K := K) (tick := tick) allocation m)
    (side : Fin 3) (w : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m)
    (hw : AllFieldHistoryRecovery.Used F allocation m ε e (sigma side) w) :
    Admissible (K := K) (tick := tick) allocation m ε sigma side
      (projectTarget (K := K) (tick := tick) allocation m sigma e) (projectRaw (K := K) (tick := tick) allocation m sigma w) := by
  obtain ⟨x, y, z, hq, rfl⟩ := hw
  have hi :
      AllFieldHistoryRecovery.idealSide allocation m ε 0 e x ∧
      AllFieldHistoryRecovery.idealSide allocation m ε 1 e y ∧
      AllFieldHistoryRecovery.idealSide allocation m ε 2 e z := by
    by_contra hn
    apply hq
    rw [AllFieldHistoryRecovery.ideal_eq_delete_source F allocation m ε e]
    exact ite_eq_right hn
  have ht := AllFieldHistoryRecovery.ideal_support_weights F allocation m ε e x y z hq
  have hs (s : Fin 3) :
      AllFieldHistoryRecovery.idealSide allocation m ε s e
          (AllFieldHistoryRecovery.sideVariable s x y z) ∧
        AllFieldHistoryRecovery.sideWeights allocation m s e
          (AllFieldHistoryRecovery.sideVariable s x y z) := by
    fin_cases s
    · exact ⟨hi.1, ht.1⟩
    · exact ⟨hi.2.1, ht.2.1⟩
    · exact ⟨hi.2.2, ht.2.2⟩
  refine ⟨?_, ?_⟩
  · exact (idealSide_iff_all_groups allocation m ε
      (sigma side) e _).mp (hs (sigma side)).1 sigma
  · intro h j
    exact (hs (sigma side)).2 h.val j

theorem used_project_covered (F : Type*) [CommRing F]
    (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (e : AllFieldHistoryRecovery.Targets (K := K) (tick := tick) allocation m)
    (side : Fin 3) (w : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m)
    (hw : AllFieldHistoryRecovery.Used F allocation m ε e (sigma side) w) :
    ∃ o ∈ (data (K := K) (tick := tick) allocation m ε sigma).orbits (projectTarget (K := K) (tick := tick) allocation m sigma e),
      (side, projectRaw (K := K) (tick := tick) allocation m sigma w) ∈
        (data (K := K) (tick := tick) allocation m ε sigma).full (projectTarget (K := K) (tick := tick) allocation m sigma e) o :=
  admissible_covered allocation m ε sigma side _ _
    (used_project_admissible F allocation m ε sigma e side w hw)

end MatrixMultiplication.AllFieldGroupAdmissible

end

end OAI
