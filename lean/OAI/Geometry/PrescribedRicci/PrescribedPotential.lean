import Mathlib
import OAI.Geometry.PrescribedRicci.DimensionOnePotential
import OAI.Geometry.PrescribedRicci.DimensionZeroPotential
import OAI.Geometry.PrescribedRicci.PositivePathClosedness

namespace OAI

/-! Prescribed Potential. -/

section

 

noncomputable section
namespace Anticanonical.SourceSmooth

theorem prescribedPotentialViaEnergy (d : ℕ) (X : Type) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] (A : ComplexAtlas d X)
    (P : A.ProjectiveEmbedding) (h : SemipositiveAnticanonicalMetric A) :
    HasPrescribedVolumePotential P h := by
  rcases d with _ | d
  · obtain ⟨φ,b,hφ⟩ := volumePath_zeroDim_one (projectiveBackground P) h
    exact volumePath_one P h φ b hφ
  rcases d with _ | d
  · exact prescribedPotential_dimensionOne X A P h
  · obtain ⟨φ,b,hφ⟩ := volumePath_one_exists (projectiveBackground P) h (by omega)
    exact volumePath_one P h φ b hφ

end Anticanonical.SourceSmooth

end
end

end OAI
