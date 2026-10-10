import Mathlib
import OAI.Geometry.Cannon.Flows.Domain

namespace OAI

section
section
section
noncomputable section
section
section
section
namespace CannonApprox

open CannonMagnification CannonCrossEnergy Set Metric Filter Topology MeasureTheory

lemma onDomain_image_eq {X : Type*} [TopologicalSpace X] {Ω : Set X}
    (u : C(Ω,ℝ)) (A : Set X) (hA : A ⊆ Ω) :
    onDomain u '' A = u '' (Subtype.val ⁻¹' A) := by
  ext t
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨⟨x,hA hx⟩,hx,(onDomain_eq u x (hA hx)).symm⟩
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x,hx,onDomain_eq u x x.property⟩

end CannonApprox

end
end
end
end
end
end
end

end OAI
