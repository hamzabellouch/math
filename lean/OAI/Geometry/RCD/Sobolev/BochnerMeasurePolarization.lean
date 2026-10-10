import OAI.Geometry.RCD.Coordinates.RegularBochnerMeasure

namespace OAI

/-! # The full off-diagonal Bochner test identity -/

open MeasureTheory
open scoped BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X E : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- Diagonal identities determine the integral of every off-diagonal
signed measure, with no absolute-continuity assumption. -/
theorem PositiveBilinearMeasure.polarized_test (M : PositiveBilinearMeasure X E)
    (q : X →ᵇ ℝ) (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hB : ∀ a b, B a b=B b a)
    (h : ∀ a, (∫ x, q x ∂M.measure a)=B a a) (a b : E) :
    signedTestIntegral q (M.bilinear a b)=B a b := by
  have hd (v : E) : signedTestIntegral q (M.bilinear v v)=B v v := by
    rw [← M.measure_toSignedMeasure, signedTestIntegral]
    exact (VectorMeasure.integral_toSignedMeasure).trans (h v)
  have hh := hd (a+b)
  simp only [map_add,LinearMap.add_apply] at hh
  rw [hd a,hd b,M.symmetric b a,hB b a] at hh
  linarith only [hh]

end RegularPointCoordinates

end

end OAI
