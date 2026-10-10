import OAI.Geometry.RCD.Harmonic.UnboundedCaccioppoli

namespace OAI

/-! # Energy of a Lipschitz cutoff times an arbitrary Sobolev function -/

open Set Filter MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The usual two-term product energy bound, with no boundedness hypothesis
on the Sobolev factor. -/
theorem energy_cutoffCLM_le (u η : SobolevSpace μ hQ)
    {v : X → ℝ} {L B A : ℝ≥0} (hv : LipschitzWith L v)
    (hs : HasCompactSupport v) (hb : ∀ x, |v x| ≤ B) (hn : ∀ x, 0 ≤ v x)
    (hrep : SobolevSpace.toLp μ hQ η =ᵐ[μ] v)
    (hgrad : ∀ᵐ x ∂μ, |SobolevSpace.minimalSlope μ hQ η x| ≤ A) :
    let z := SobolevSpace.cutoffCLM μ hQ hv hs hb hn u
    energyForm μ hQ z z ≤
      2*(∫ x, (SobolevSpace.toLp μ hQ η x)^2*(SobolevSpace.minimalSlope μ hQ u x)^2 ∂μ)+
      2*∫ x, (SobolevSpace.toLp μ hQ u x)^2*(SobolevSpace.minimalSlope μ hQ η x)^2 ∂μ := by
  intro z
  have hη : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ η x| ≤ B := by
    filter_upwards [hrep] with x hx
    rw [hx]
    exact hb x
  have hi1 := bounded_square_weight_integrable μ (SobolevSpace.toLp μ hQ η)
    (SobolevSpace.minimalSlope μ hQ u) hη
  have hi2 : Integrable (fun x => (SobolevSpace.toLp μ hQ u x)^2*
      (SobolevSpace.minimalSlope μ hQ η x)^2) μ := by
    exact (bounded_square_weight_integrable μ (SobolevSpace.minimalSlope μ hQ η)
      (SobolevSpace.toLp μ hQ u) hgrad).congr (Eventually.of_forall fun x => mul_comm _ _)
  rw [← integral_localGamma_eq_energyForm,← integral_const_mul,← integral_const_mul,
    ← integral_add (hi1.const_mul 2) (hi2.const_mul 2)]
  apply integral_mono_ae (localGamma_memL1 μ hQ z z)
    ((hi1.const_mul 2).add (hi2.const_mul 2))
  filter_upwards [localGamma_cutoffCLM μ hQ u η z hv hs hb hn hrep,
    localGamma_cutoffCLM_right μ hQ u η u hv hs hb hn hrep,
    localGamma_cutoffCLM_right μ hQ u η η hv hs hb hn hrep,
    localGamma_self μ hQ u,localGamma_self μ hQ η,
    localGamma_comm μ hQ η u,localGamma_abs_le μ hQ u η,hrep] with
    x hz hu hη hsU hsE hc hγ hr
  change localGamma μ hQ z z x ≤ _
  change localGamma μ hQ u z x = _ at hu
  change localGamma μ hQ η z x = _ at hη
  change localGamma μ hQ z z x = _ at hz
  rw [hz,hu,hη,hsU,hsE,hc,← hr]
  have habs : |SobolevSpace.toLp μ hQ η x * SobolevSpace.toLp μ hQ u x *
      localGamma μ hQ u η x| ≤
      |SobolevSpace.toLp μ hQ η x| * SobolevSpace.minimalSlope μ hQ u x*
      (|SobolevSpace.toLp μ hQ u x| * SobolevSpace.minimalSlope μ hQ η x) := by
    calc
      _ = (|SobolevSpace.toLp μ hQ η x| * |SobolevSpace.toLp μ hQ u x|)*
          |localGamma μ hQ u η x| := by rw [abs_mul,abs_mul]
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left hγ
          (mul_nonneg (abs_nonneg (SobolevSpace.toLp μ hQ η x))
            (abs_nonneg (SobolevSpace.toLp μ hQ u x)))
        nlinarith only [hh]
  have hsq := sq_nonneg (|SobolevSpace.toLp μ hQ η x| * SobolevSpace.minimalSlope μ hQ u x-
    |SobolevSpace.toLp μ hQ u x| * SobolevSpace.minimalSlope μ hQ η x)
  simp only [sub_sq,mul_pow,sq_abs] at hsq
  have hh := (le_abs_self _).trans habs
  dsimp only [Pi.add_apply]
  nlinarith only [hh,hsq]

end RegularPointCoordinates

end

end OAI
