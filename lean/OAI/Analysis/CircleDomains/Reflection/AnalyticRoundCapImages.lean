import OAI.Analysis.CircleDomains.Reflection.ReflectedCircleImages
import OAI.Analysis.CircleDomains.Topology.HomeomorphRoundDiskImage

namespace OAI

/-! The actual invariant-coefficient straightening carries every closed
analytic Jordan cap onto a positive-radius closed round disk. -/
open Set Function Metric
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace AnalyticReflectionData
variable {I : Type*} [Finite I] {C : FiniteJordanConfiguration I}

lemma exists_round_cap_images (D : AnalyticReflectionData C) :
    ∃s : I → ℝ,(∀i,0<s i) ∧ ∀i,
      (D.comparison.trans D.principal) '' closure (jordanInterior (C.hole i))=
        closedBall (D.principal (D.center i)) (s i) := by
  choose s hs he using D.exists_round_boundary_image
  refine ⟨s,hs,?_⟩
  intro i
  change (D.principal ∘ D.comparison) '' closure (jordanInterior (C.hole i))=_
  rw [image_comp,D.cap_image]
  exact homeomorph_image_closedBall_of_sphere D.principal (D.radius_pos i) (hs i) (he i)

end AnalyticReflectionData
end CircleDomainRigidity

end

end OAI
