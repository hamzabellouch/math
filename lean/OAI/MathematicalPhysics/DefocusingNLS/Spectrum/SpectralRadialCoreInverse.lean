import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialObservation
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

namespace OAI

/-! The constrained inverse is the Riesz representative projected to the closed core. -/

open InnerProductSpace
namespace DefocusingNLS

instance spectralRadialCore_projection (R l : ℝ) :
    (spectralRadialCoreSubspace R l).HasOrthogonalProjection := by
  let : CompleteSpace (spectralRadialCoreSubspace R l) := spectralRadialCoreEnergy_complete R l
  exact .ofCompleteSpace _

noncomputable def spectralRadialCoreInverse (R l : ℝ) :
    StrongDual ℝ (SpectralRadialPairEnergy R) →L[ℝ] SpectralRadialPairEnergy R :=
  (spectralRadialCoreSubspace R l).starProjection.comp
    (toDual ℝ (SpectralRadialPairEnergy R)).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem spectralRadialCoreInverse_mem (R l : ℝ) (F : StrongDual ℝ (SpectralRadialPairEnergy R)) :
    spectralRadialCoreInverse R l F ∈ spectralRadialCoreSubspace R l :=
  (spectralRadialCoreSubspace R l).starProjection_apply_mem _

theorem spectralRadialCoreInverse_equation (R l : ℝ)
    (F : StrongDual ℝ (SpectralRadialPairEnergy R)) (v : SpectralRadialCoreEnergy R l) :
    inner ℝ (spectralRadialCoreInverse R l F) (v : SpectralRadialPairEnergy R)=F v := by
  change inner ℝ ((spectralRadialCoreSubspace R l).starProjection
    ((toDual ℝ (SpectralRadialPairEnergy R)).symm F)) (v : SpectralRadialPairEnergy R)=_
  rw [(spectralRadialCoreSubspace R l).inner_starProjection_left_eq_right,
    (spectralRadialCoreSubspace R l).starProjection_mem_subspace_eq_self v]
  exact toDual_symm_apply (𝕜 := ℝ) (E := SpectralRadialPairEnergy R)

theorem spectralRadialCoreInverse_unique (R l : ℝ)
    (F : StrongDual ℝ (SpectralRadialPairEnergy R)) (u : SpectralRadialPairEnergy R)
    (hu : u ∈ spectralRadialCoreSubspace R l)
    (he : ∀ v : SpectralRadialCoreEnergy R l, inner ℝ u (v : SpectralRadialPairEnergy R)=F v) :
    u=spectralRadialCoreInverse R l F := by
  symm
  apply (spectralRadialCoreSubspace R l).eq_starProjection_of_mem_of_inner_eq_zero hu
  intro w hw
  rw [inner_sub_left]
  have hr : inner ℝ ((toDual ℝ (SpectralRadialPairEnergy R)).symm F) w=F w :=
    toDual_symm_apply (𝕜 := ℝ) (E := SpectralRadialPairEnergy R)
  change inner ℝ ((toDual ℝ (SpectralRadialPairEnergy R)).symm F) w-inner ℝ u w=0
  rw [hr,he ⟨w,hw⟩,sub_self]

theorem spectralRadialCoreInverse_norm (R l : ℝ) (F : StrongDual ℝ (SpectralRadialPairEnergy R)) :
    ‖spectralRadialCoreInverse R l F‖ ≤ ‖F‖ := by
  exact ((spectralRadialCoreSubspace R l).norm_starProjection_apply_le _).trans_eq
    ((toDual ℝ (SpectralRadialPairEnergy R)).symm.norm_map F)

theorem spectralRadialCoreInverse_observation_compact (R l : ℝ) (hR : 0 < R) :
    IsCompactOperator (((spectralRadialObservation R hR).restrictScalars ℝ).comp
      (spectralRadialCoreInverse R l)) :=
  (spectralRadialObservation_compact R hR).comp_clm (spectralRadialCoreInverse R l)

end DefocusingNLS

end OAI
