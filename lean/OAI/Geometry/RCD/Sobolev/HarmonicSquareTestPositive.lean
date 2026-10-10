import OAI.Geometry.RCD.Harmonic.EuclideanHarmonicSquare

namespace OAI

/-! # Nonnegative compact tests against a squared harmonic function -/

open Set MeasureTheory Laplacian
open scoped ContDiff
noncomputable section
namespace RegularPointCoordinates

theorem harmonic_square_test_nonneg {n : ℕ} {f ψ : Euclidean n → ℝ}
    (hf : ContDiff ℝ 2 f) (hψ : ContDiff ℝ 2 ψ) (hs : HasCompactSupport ψ)
    (hψ0 : ∀ x, 0≤ψ x) (hh : ∀ x∈tsupport ψ, (Δ f) x=0) :
    0≤∫ x, (f x)^2*(Δ ψ) x := by
  rw [integral_laplacian_commute (hf.pow 2) hψ hs]
  apply integral_nonneg
  intro x
  change 0≤(Δ (fun z => (f z)^2)) x*ψ x
  by_cases hx : ψ x=0
  · rw [hx,mul_zero]
  · exact mul_nonneg (harmonic_square_laplacian_nonneg hf x (hh x (subset_tsupport ψ hx))) (hψ0 x)

end RegularPointCoordinates

end

end OAI
