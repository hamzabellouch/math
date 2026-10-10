import Mathlib
import OAI.Geometry.PrescribedPotential.BoundedPathContinuation
import OAI.Geometry.PrescribedPotential.UniformPathSobolev

namespace OAI

/-! Prescribed Potential. -/

section

 
noncomputable section
namespace Anticanonical.SourceSmooth
open GlobalElliptic

 

theorem prescribedPotential (d : ℕ) (X : Type) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] (A : ComplexAtlas d X)
    (P : A.ProjectiveEmbedding) (h : SemipositiveAnticanonicalMetric A) :
    HasPrescribedVolumePotential P h := by
  obtain ⟨S,⟨D⟩⟩ := exists_gluingData (projectiveBackground P)
  let x₀ : X := Classical.choice (inferInstance : Nonempty X)
  exact prescribedPotential_of_path_bounds P h D x₀ (D.pathSobolevBounds h x₀)

end Anticanonical.SourceSmooth

end
end

end OAI
