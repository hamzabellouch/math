import OAI.Geometry.RCD.Sobolev.CutoffProductEnergy

namespace OAI

/-! # Pointwise weak-gradient bound for a Sobolev cutoff product -/

open Set Filter MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The two-term cutoff energy inequality before integration. -/
theorem minimalSlope_cutoffCLM_sq_le (u η : SobolevSpace μ hQ)
    {v : X → ℝ} {L B : ℝ≥0} (hv : LipschitzWith L v)
    (hs : HasCompactSupport v) (hb : ∀ x, |v x| ≤ B) (hn : ∀ x, 0 ≤ v x)
    (hrep : SobolevSpace.toLp μ hQ η =ᵐ[μ] v) :
    let z := SobolevSpace.cutoffCLM μ hQ hv hs hb hn u
    ∀ᵐ x ∂μ, (SobolevSpace.minimalSlope μ hQ z x)^2 ≤
      2*(SobolevSpace.toLp μ hQ η x)^2*(SobolevSpace.minimalSlope μ hQ u x)^2+
      2*(SobolevSpace.toLp μ hQ u x)^2*(SobolevSpace.minimalSlope μ hQ η x)^2 := by
  intro z
  filter_upwards [localGamma_cutoffCLM μ hQ u η z hv hs hb hn hrep,
    localGamma_cutoffCLM_right μ hQ u η u hv hs hb hn hrep,
    localGamma_cutoffCLM_right μ hQ u η η hv hs hb hn hrep,
    localGamma_self μ hQ u,localGamma_self μ hQ η,
    localGamma_comm μ hQ η u,localGamma_abs_le μ hQ u η,hrep,
    localGamma_self μ hQ z] with
    x hz hu hη hsU hsE hc hγ hr hsZ
  rw [← hsZ]
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
  nlinarith only [hh,hsq]

end RegularPointCoordinates

end

end OAI
