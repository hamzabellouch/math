import OAI.NumberTheory.Ostmann.Characters.CharacterLogDerivativePole
import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothDirichletIntegral

namespace OAI

/-! # The exact local zero contributions in the smooth contour integral -/

namespace Ostmann

open Filter
open scoped Topology

noncomputable def smoothContourWeight (X : ℝ) (s : ℂ) : ℂ :=
  (X : ℂ) ^ s * primeMeanMellin s

theorem smoothContourWeight_differentiable (X : ℝ) (hX : 0 < X) :
    Differentiable ℂ (smoothContourWeight X) :=
  (differentiable_id.const_cpow (.inl (by exact_mod_cast hX.ne'))).mul
    primeMeanMellin_differentiable

theorem smoothContourWeight_vertical (X t : ℝ) :
    smoothContourWeight X (primeMellinLine t) = primeVerticalWeight X t := rfl

/-- Every zero contributes its negative analytic multiplicity times the
literal Mellin weight. No zero is replaced by a formal pole label. -/
theorem smoothContour_zero_residue (χ : PrimitiveComplexCharacter)
    (X : ℝ) (hX : 0 < X) (z : ℂ) :
    Tendsto (fun s => (s - z) *
      ((-deriv χ.L s / χ.L s) * smoothContourWeight X s)) (𝓝[≠] z)
      (𝓝 (-(analyticOrderNatAt χ.L z : ℂ) * smoothContourWeight X z)) := by
  have hW : Tendsto (smoothContourWeight X) (𝓝 z) (𝓝 (smoothContourWeight X z)) :=
    (smoothContourWeight_differentiable X hX).continuous.continuousAt.tendsto
  have h := (χ.logDeriv_residue_limit z).neg.mul (hW.mono_left nhdsWithin_le_nhds)
  convert h using 1
  funext s
  simp only [logDeriv_apply]
  ring

end Ostmann

end OAI
