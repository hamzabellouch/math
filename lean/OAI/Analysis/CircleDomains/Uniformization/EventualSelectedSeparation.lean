import OAI.Analysis.CircleDomains.Uniformization.CircularizationShift
import OAI.Analysis.CircleDomains.Uniformization.SelectedHoleSeparation
import OAI.Analysis.CircleDomains.Selection.SelectedRadiusLowerBound

namespace OAI

/-! Uniform radius and separation estimates for arbitrary Jordan input,
by restarting the actual iteration after its first analytic cycle. -/
open Set Function Filter Metric Complex
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace FiniteJordanConfiguration

lemma selectedRadii_eventual_lower_bound {m:ℕ} (C:FiniteJordanConfiguration (Fin (m+1))) :
    ∃δ:ℝ,0<δ ∧ ∀n (i:Fin (m+1)),
      δ ≤ selectedRadius C (cyclicSchedule m) (visitTime (n+1) i) := by
  obtain ⟨δ,hδ,hb⟩ := selectedRadii_common_lower_bound
    (iterate C (cyclicSchedule m) (m+1)) (fun i => cyclic_iterate_analytic C le_rfl i)
  refine ⟨δ,hδ,?_⟩
  intro n i
  rw [visitTime_succ,selectedRadius_cycle_add]
  exact hb n i

lemma selectedCircles_eventual_separation {m:ℕ} (C:FiniteJordanConfiguration (Fin (m+1))) :
    ∃ε:ℝ,0<ε ∧ ∀n (i j:Fin (m+1)),j≠i → ∀y,
      y∈closure (jordanInterior ((iterate C (cyclicSchedule m) (visitTime (n+1) i+1)).hole j)) →
      selectedRadius C (cyclicSchedule m) (visitTime (n+1) i)+ε≤
        ‖y-selectedCenter C (cyclicSchedule m) (visitTime (n+1) i)‖ := by
  obtain ⟨ε,hε,hb⟩ := selectedCircles_other_hole_separation
    (iterate C (cyclicSchedule m) (m+1)) (fun i => cyclic_iterate_analytic C le_rfl i)
  refine ⟨ε,hε,?_⟩
  intro n i j hji y hy
  rw [visitTime_succ,selectedRadius_cycle_add,selectedCenter_cycle_add]
  apply hb n i j hji y
  rw [visitTime_succ,Nat.add_assoc,iterate_cycle_add] at hy
  exact hy

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
