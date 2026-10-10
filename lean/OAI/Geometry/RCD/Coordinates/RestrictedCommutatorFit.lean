import OAI.Geometry.RCD.Coordinates.ActualFitCommutator
import OAI.Geometry.RCD.Coordinates.RadialFitRestriction
import OAI.Geometry.RCD.Harmonic.RadialDerivativeError

namespace OAI

/-! # Restricting the full commutator to the common radial-fit ball -/

open Set MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The chosen fits only need to represent the radial derivatives on the
smaller common ball. Restriction loses precisely the given volume ratio. -/
theorem normalized_commutator_restrict {Ω Ω' : Set X}
    (hsub : Ω' ⊆ Ω) (hpos : 0 < μ.real Ω) (hpos' : 0 < μ.real Ω')
    (f v u g₀ h₀ g h : SobolevSpace μ hQ) {Cf Cv C E : ℝ}
    (hf : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ f f x ≤ Cf)
    (hv : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ v v x ≤ Cv)
    (hg₀ : SobolevSpace.toLp μ hQ g₀ =ᵐ[μ.restrict Ω] localGamma μ hQ f u)
    (hh₀ : SobolevSpace.toLp μ hQ h₀ =ᵐ[μ.restrict Ω] localGamma μ hQ v u)
    (hg : SobolevSpace.toLp μ hQ g =ᵐ[μ.restrict Ω'] localGamma μ hQ f u)
    (hh : SobolevSpace.toLp μ hQ h =ᵐ[μ.restrict Ω'] localGamma μ hQ v u)
    (hE : 0 ≤ E) (hvol : μ.real Ω ≤ C * μ.real Ω')
    (he : (μ.real Ω)⁻¹ * (∫ x in Ω,
      (localGamma μ hQ v g₀ x - localGamma μ hQ f h₀ x - localGamma μ hQ v u x) ^ 2 ∂μ) ≤ E) :
    (μ.real Ω')⁻¹ * (∫ x in Ω',
      (localGamma μ hQ v g x - localGamma μ hQ f h x - localGamma μ hQ v u x) ^ 2 ∂μ) ≤ C * E := by
  have hvg : MemLp (localGamma μ hQ v g₀) 2 (μ.restrict Ω) :=
    (memLp_congr_ae (ae_restrict_of_ae (localGamma_comm μ hQ g₀ v))).mp
      (localGamma_memLp_two_of_bound μ hQ Ω g₀ v hv)
  have hfh : MemLp (localGamma μ hQ f h₀) 2 (μ.restrict Ω) :=
    (memLp_congr_ae (ae_restrict_of_ae (localGamma_comm μ hQ h₀ f))).mp
      (localGamma_memLp_two_of_bound μ hQ Ω h₀ f hf)
  have hvu : MemLp (localGamma μ hQ v u) 2 (μ.restrict Ω) :=
    (memLp_congr_ae (ae_restrict_of_ae (localGamma_comm μ hQ u v))).mp
      (localGamma_memLp_two_of_bound μ hQ Ω u v hv)
  have hsmall := average_nonneg_le_of_subset μ hsub hpos' hpos
    ((hvg.sub hfh).sub hvu).integrable_sq (fun x => sq_nonneg _) hE hvol he
  have htransfer := commutator_error_transfer μ hQ f v u g₀ h₀ g h
    (ae_restrict_of_ae_restrict_of_subset hsub hg₀)
    (ae_restrict_of_ae_restrict_of_subset hsub hh₀) hg hh le_rfl
  exact (mul_le_mul_of_nonneg_left htransfer (by positivity)).trans hsmall

end RegularPointCoordinates

end

end OAI
