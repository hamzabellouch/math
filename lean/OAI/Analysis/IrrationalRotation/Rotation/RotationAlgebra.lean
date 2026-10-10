import OAI.Analysis.IrrationalRotation.Rotation.Rotation
import OAI.Analysis.IrrationalRotation.Analysis.GeneratedVonNeumann
import OAI.Analysis.IrrationalRotation.Rotation.ContinuousCircleImage

namespace OAI

noncomputable section
namespace Invariant233.Rotation

theorem U_mem_algebra (θ : ℝ) : U ∈ algebra θ :=
  subset_vonNeumannGenerated _ (Set.mem_insert U _)

theorem V_mem_algebra (θ : ℝ) : V θ ∈ algebra θ :=
  subset_vonNeumannGenerated _ (Set.mem_insert_of_mem U (Set.mem_singleton _))

theorem representation_mem_algebra (θ : ℝ) (a : C(Circle, ℂ)) :
    representation θ a ∈ algebra θ :=
  ContinuousCircleImage.image_mem (representationStarAlgHom θ) (representation_continuous θ)
    (algebra θ) (V_mem_algebra θ) a

theorem weighted_mem_algebra (θ : ℝ) (a : C(Circle, ℂ)) :
    weighted θ a ∈ algebra θ :=
  mul_mem (U_mem_algebra θ) (representation_mem_algebra θ a)

theorem weightedReal_mem_algebra (θ : ℝ) (f : C(Circle, ℝ)) :
    weightedReal θ f ∈ algebra θ :=
  weighted_mem_algebra θ (complexWeight f)

theorem representation_unique (θ : ℝ)
    (Φ : C(Circle, ℂ) →⋆ₐ[ℂ] (Hilbert →L[ℂ] Hilbert))
    (hΦ : Continuous Φ) (hV : Φ character = V θ) :
    Φ = representationStarAlgHom θ :=
  ContinuousCircleImage.hom_ext_character Φ (representationStarAlgHom θ)
    hΦ (representation_continuous θ) hV

end Invariant233.Rotation

end

end OAI
