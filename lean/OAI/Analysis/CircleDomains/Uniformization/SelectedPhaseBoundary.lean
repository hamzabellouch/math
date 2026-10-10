import OAI.Analysis.CircleDomains.Transfer.GlobalCoreExtension
import OAI.Analysis.CircleDomains.Uniformization.CircularizationPhaseLimit
import OAI.Analysis.CircleDomains.Topology.SphereCompactFrontier

namespace OAI

/-! Exact finite-plane circle values for the labelled compact extension
at a selected phase of the actual cyclic iteration. -/
open Set Function Filter Metric Complex
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma frontier_sphere_closedBall (c:ℂ) {r:ℝ} (hr:0<r) :
    frontier (((↑):ℂ→Sphere) '' closedBall c r)=((↑):ℂ→Sphere) '' sphere c r := by
  have h := frontier_closedTerminalCap (roundJordanAt c r hr)
  change frontier (((↑):ℂ→Sphere) '' closure (jordanInterior (roundJordanAt c r hr)))=
    ((↑):ℂ→Sphere) '' frontier (jordanInterior (roundJordanAt c r hr)) at h
  rw [roundJordanAt_closure,roundJordanAt_interior,frontier_ball c hr.ne'] at h
  exact h

namespace FiniteJordanConfiguration
variable {I:Type*} [Finite I]

omit [Finite I] in
lemma boundary_norm_of_round_image (C D:FiniteJordanConfiguration I) (i:I)
    {E:Sphere→Sphere} {c:ℂ} {r:ℝ} (hr:0<r)
    (hround:jordanInterior (D.hole i)=ball c r)
    (himage:E '' frontier (closedTerminalCap (C.hole i))=
      frontier (closedTerminalCap (D.hole i)))
    {x:ℂ} (hx:x∈frontier (jordanInterior (C.hole i))) :
    ‖finiteCoord (E (x:Sphere))-c‖=r := by
  have hp : E (x:Sphere)∈frontier (closedTerminalCap (D.hole i)) := by
    rw [←himage]
    refine ⟨(x:Sphere),?_,rfl⟩
    rw [frontier_closedTerminalCap]
    exact ⟨x,hx,rfl⟩
  have hcap : closedTerminalCap (D.hole i)=((↑):ℂ→Sphere) '' closedBall c r := by
    rw [closedTerminalCap,hround,closure_ball c hr.ne']
  rw [hcap,frontier_sphere_closedBall c hr] at hp
  obtain ⟨w,hw,he⟩ := hp
  rw [←he,finiteCoord_coe]
  exact mem_sphere_iff_norm.mp hw

lemma selected_phase_boundary_norm {m:ℕ} (C:FiniteJordanConfiguration (Fin (m+1)))
    (i:Fin (m+1)) (n:ℕ) {E:Sphere→Sphere}
    (himage:∀j,E '' frontier (closedTerminalCap (C.hole j))=
      frontier (closedTerminalCap ((iterate C (cyclicSchedule m) (visitTime n i+1)).hole j)))
    {x:ℂ} (hx:x∈frontier (jordanInterior (C.hole i))) :
    ‖finiteCoord (E (x:Sphere))-selectedCenter C (cyclicSchedule m) (visitTime n i)‖=
      selectedRadius C (cyclicSchedule m) (visitTime n i) := by
  apply boundary_norm_of_round_image C (iterate C (cyclicSchedule m) (visitTime n i+1)) i
    (selectedRadius_pos C (cyclicSchedule m) (visitTime n i)) ?_ (himage i) hx
  change jordanInterior ((chosenStep (iterate C (cyclicSchedule m) (visitTime n i))
    (cyclicSchedule m (visitTime n i))).target.hole i)=
      ball (chosenStep (iterate C (cyclicSchedule m) (visitTime n i))
        (cyclicSchedule m (visitTime n i))).center
        (chosenStep (iterate C (cyclicSchedule m) (visitTime n i))
          (cyclicSchedule m (visitTime n i))).radius
  have hh := (chosenStep (iterate C (cyclicSchedule m) (visitTime n i))
    (cyclicSchedule m (visitTime n i))).selected
  simpa only [cyclicSchedule_visit] using hh

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
