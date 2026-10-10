import OAI.Analysis.CircleDomains.Reflection.ClosedExteriorCorrespondence
import OAI.Analysis.CircleDomains.Reflection.AnalyticCircularization

namespace OAI

/-! Compact boundary correspondences for the actual one-hole maps used
by the finite circularization iteration. -/
open Set Function Filter Metric
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace FiniteJordanConfiguration

variable {I:Type*} [Finite I] {C:FiniteJordanConfiguration I} {j:I}

omit [Finite I] in
lemma Step.closed_exterior_correspondence (q:Step C j)
    (ha:IsAnalyticJordanCap (C.hole j)) :
    ∃e : closure (closedTerminalCap (C.hole j))ᶜ ≃ₜ
        closure ((((↑):ℂ→Sphere) '' closedBall q.center q.radius)ᶜ),
      ∀p : closure (closedTerminalCap (C.hole j))ᶜ,
        (p:Sphere)∈(closedTerminalCap (C.hole j))ᶜ → (e p:Sphere)=q.map p :=
  exists_closed_exterior_correspondence ha q.radius_pos q.exterior_conformal

lemma cyclic_closed_exterior_correspondence {m:ℕ}
    (C:FiniteJordanConfiguration (Fin (m+1))) {n:ℕ} (hn:m+1≤n) :
    ∃e : closure (closedTerminalCap ((iterate C (cyclicSchedule m) n).hole
        (cyclicSchedule m n)))ᶜ ≃ₜ
        closure ((((↑):ℂ→Sphere) '' closedBall (selectedCenter C (cyclicSchedule m) n)
          (selectedRadius C (cyclicSchedule m) n))ᶜ),
      ∀p : closure (closedTerminalCap ((iterate C (cyclicSchedule m) n).hole
          (cyclicSchedule m n)))ᶜ,
        (p:Sphere)∈(closedTerminalCap ((iterate C (cyclicSchedule m) n).hole
        (cyclicSchedule m n)))ᶜ → (e p:Sphere)=stageMap C (cyclicSchedule m) n p :=
  (chosenStep (iterate C (cyclicSchedule m) n) (cyclicSchedule m n)).closed_exterior_correspondence
    (cyclic_iterate_analytic C hn _)

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
