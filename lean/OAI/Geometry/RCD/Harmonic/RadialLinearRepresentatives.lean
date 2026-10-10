import OAI.Geometry.RCD.Harmonic.LocalRadialDerivative

namespace OAI

/-! # Finite radial families preserve all constant covectors -/

open Set MeasureTheory
open scoped BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Once the basis radial derivatives have Sobolev representatives, their
linear combinations are the radial derivatives of every coordinate covector. -/
theorem localRadialDerivative_column {n : ℕ} (Ω : Set X)
    (f : SobolevSpace μ hQ) {B : ℝ}
    (hf : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ f f x ≤ B)
    (u g : Fin n → SobolevSpace μ hQ)
    (hg : ∀ j, SobolevSpace.toLp μ hQ (g j) =ᵐ[μ.restrict Ω] localGamma μ hQ f (u j))
    (b : Euclidean n) :
    localRadialDerivative μ hQ Ω f hf (sobolevColumnMap μ hQ u b) =
      SobolevSpace.restrictLp μ hQ Ω (sobolevColumnMap μ hQ g b) := by
  simp only [sobolevColumnMap_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro j _
  rw [localRadialDerivative_eq_restrict μ hQ Ω f (u j) (g j) hf (hg j)]

/-- The derivative kills every compactly extended local constant. -/
theorem localRadialDerivative_constant (Ω : Set X) (f q : SobolevSpace μ hQ) {B : ℝ}
    (hf : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ f f x ≤ B) (c : ℝ)
    (hq : SobolevSpace.toLp μ hQ q =ᵐ[μ.restrict Ω] fun _ => c) :
    localRadialDerivative μ hQ Ω f hf q = 0 := by
  have hh := localRadialDerivative_eq_of_constant_difference μ hQ Ω f q 0 hf c
    (by simpa only [sub_zero] using hq)
  simpa only [map_zero] using hh

end RegularPointCoordinates

end

end OAI
