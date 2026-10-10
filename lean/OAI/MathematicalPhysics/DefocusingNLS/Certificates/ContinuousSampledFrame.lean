import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzSampleContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.SampledSchwartzFrame
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLocalizationContinuity

namespace OAI

/-! # Continuous sampled frames and their finite coordinate matrices -/

open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

attribute [local irreducible] sampledSchwartzFrame expandingCoordinates homogeneousLocalizationCLM

theorem continuous_sampledSchwartzFrame (a k : ℝ) (ha1 : a < 1) (hk : 8 < k)
    (B : F →ₗ[ℝ] 𝓢(E, ℂ)) : Continuous (sampledSchwartzFrame a k ha1 hk B) := by
  classical
  apply continuous_clm_apply.mpr
  intro v
  have he (L : Radius) : sampledSchwartzFrame a k ha1 hk B L v =
      ∑ i, (Module.finBasis ℝ F).repr v i •
        schwartzTorusSample a k L.1 ha1 hk L.2
          (radianFourierKernel (B ((Module.finBasis ℝ F) i))) := by
    conv_lhs => rw [← (Module.finBasis ℝ F).sum_repr v]
    simp only [map_sum, map_smul, sampledSchwartzFrame_basis]
  simp_rw [he]
  exact continuous_finsetSum _ (fun i _ =>
    (continuous_const : Continuous (fun _ : Radius => (Module.finBasis ℝ F).repr v i)).smul
      (continuous_schwartzTorusSample a k ha1 hk _))

theorem continuous_sampledSchwartzFrame_coordinates (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (χ : 𝓢(E, ℂ))
    (π : HomogeneousY a k →L[ℝ] F) (B : F →ₗ[ℝ] 𝓢(E, ℂ)) :
    Continuous (fun L : Radius => (expandingCoordinates a k ha ha1 hk χ π L).comp
      (sampledSchwartzFrame a k ha1 hk B L)) := by
  apply continuous_clm_apply.mpr
  intro v
  have hv : Continuous (fun L : Radius => sampledSchwartzFrame a k ha1 hk B L v) :=
    (continuous_sampledSchwartzFrame a k ha1 hk B).clm_apply continuous_const
  exact (continuous_expandingCoordinates_apply a k ha ha1 hk χ π).comp
    (continuous_id.prodMk hv)

end DefocusingNLS

end OAI
