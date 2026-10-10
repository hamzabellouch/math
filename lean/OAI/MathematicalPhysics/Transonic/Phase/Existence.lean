import OAI.MathematicalPhysics.Transonic.Phase.Transport
import OAI.MathematicalPhysics.Transonic.Profile.GlobalExistence

namespace OAI

section
noncomputable section
namespace SepticProfile
open Set
open scoped ContDiff

/-- A positive smooth radial phase with timelike gradient and vanishing phase
transport, together with its positive septic amplitude, in four spatial dimensions. -/
theorem exists_global_phase_input :
    ∃ P : GlobalProfile,
      (∀ y : ℝ, 0<P.H y) ∧
      (∃ Hrad : ℝ → ℝ, ContDiffOn ℝ ∞ Hrad (Ici 0) ∧
        ∀ y : ℝ, P.H y=Hrad (y^2)) ∧
      (∀ t : ℝ, 0<t → ∀ X : PhysicalSpace,
        0 < minkowskiSquare P.s0 t X ∧ phaseTransport P.s0 t X=0 ∧
        0<P.w0 t X) := by
  obtain ⟨P⟩ := globalProfile_of_exists SonicShooting.exists_global_source_profile
  exact ⟨P,P.H_pos,⟨P.radialH,P.radialH_smooth,P.H_radial⟩,
    fun t ht X => ⟨P.s0_timelike ht X,P.s0_transport ht X,P.w0_pos ht X⟩⟩

end SepticProfile

end
end

end OAI
