import OAI.Analysis.CircleDomains.Topology.PhaseUniformImageNeighborhood
import OAI.Analysis.CircleDomains.Reflection.FinitePhaseSides

namespace OAI

/-! Uniform metric collars outside the circles selected by the actual
finite construction contain no other omitted component. -/
open Set Function Filter Metric Complex
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace FiniteJordanConfiguration
variable {m:ℕ} {C:FiniteJordanConfiguration (Fin (m+1))} {i:Fin (m+1)}

lemma PhaseCollar.uniform_selected_collar (P:PhaseCollar C i) :
    ∃ε:ℝ,0<ε ∧ ∀n y,
      selectedRadius C (cyclicSchedule m) (visitTime n i)<
        ‖y-selectedCenter C (cyclicSchedule m) (visitTime n i)‖ →
      (∃w∈sphere (selectedCenter C (cyclicSchedule m) (visitTime n i))
        (selectedRadius C (cyclicSchedule m) (visitTime n i)),dist y w<ε) →
      y∈(iterate C (cyclicSchedule m) (visitTime n i+1)).planeRegion := by
  obtain ⟨ε,hε,hball⟩ := P.uniform_image_neighborhood (isCompact_sphere (0:ℂ) 1)
    (unit_circle_subset_symmetricCircleAnnulus P.radius_gt)
  refine ⟨ε,hε,?_⟩
  intro n y hy hw
  obtain ⟨w,hw,hyw⟩ := hw
  rw [←P.reflected_circle_image n] at hw
  obtain ⟨z,hz,rfl⟩ := hw
  exact P.reflected_image_outside_subset n
    ⟨hball n z hz hyw,fun h => (not_le_of_gt hy) (mem_closedBall_iff_norm.mp h)⟩

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
