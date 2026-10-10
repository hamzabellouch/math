import OAI.Geometry.RCD.Sobolev.BochnerTestForm
import OAI.Geometry.RCD.Sobolev.WeightedGammaL2Algebra
import OAI.Geometry.RCD.Sobolev.WeightedLaplacianPair
import OAI.Geometry.RCD.Sobolev.CompactBochnerTest

namespace OAI

/-! # Polarized Bochner forms on a finite regular span -/

open Set Filter MeasureTheory
open scoped NNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ) {m : ℕ}

/-- The full weak Bochner form retains both L² source terms. -/
def regularBochnerForm (K : ℝ)
    (U : Euclidean m →L[ℝ] SobolevSpace μ hQ) (D : Euclidean m →L[ℝ] Lp ℝ 2 μ)
    (H : Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] SobolevSpace μ hQ)
    (q : X →ᵇ ℝ) (ψ : SobolevSpace μ hQ) (L : Euclidean m → ℝ≥0)
    (hU : ∀ a, ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ (U a) x≤L a) :
    Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun a b => bochnerTestForm μ hQ (-K) (H a b) ψ+
      weightedLaplacianPair μ q (D a) (D b)+
      (1/2 : ℝ)*(weightedGamma μ hQ (D a) (U b) ψ+weightedGamma μ hQ (D b) (U a) ψ))
    (by
      intro a b c
      simp only [map_add,LinearMap.add_apply]
      rw [weightedGamma_lp_add_weight μ hQ (D a) (D b) (U c) ψ (L c) (hU c),
        weightedGamma_lp_add_left μ hQ (D c) (U a) (U b) ψ (L a) (L b) (hU a) (hU b)]
      ring)
    (by
      intro c a b
      simp only [map_smul,LinearMap.smul_apply,smul_eq_mul]
      rw [weightedGamma_lp_smul_weight,weightedGamma_smul_left]
      ring)
    (by
      intro a b c
      simp only [map_add,LinearMap.add_apply]
      rw [weightedGamma_lp_add_left μ hQ (D a) (U b) (U c) ψ (L b) (L c) (hU b) (hU c),
        weightedGamma_lp_add_weight μ hQ (D b) (D c) (U a) ψ (L a) (hU a)]
      ring)
    (by
      intro c a b
      simp only [map_smul,LinearMap.smul_apply,smul_eq_mul]
      rw [weightedGamma_smul_left,weightedGamma_lp_smul_weight]
      ring)

theorem regularBochnerForm_symmetric (K : ℝ)
    (U : Euclidean m →L[ℝ] SobolevSpace μ hQ) (D : Euclidean m →L[ℝ] Lp ℝ 2 μ)
    (H : Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] SobolevSpace μ hQ)
    (q : X →ᵇ ℝ) (ψ : SobolevSpace μ hQ) (L : Euclidean m → ℝ≥0)
    (hU : ∀ a, ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ (U a) x≤L a)
    (hH : ∀ a b, H a b=H b a) (a b : Euclidean m) :
    regularBochnerForm μ hQ K U D H q ψ L hU a b =
      regularBochnerForm μ hQ K U D H q ψ L hU b a := by
  change bochnerTestForm μ hQ (-K) (H a b) ψ+weightedLaplacianPair μ q (D a) (D b)+
    (1/2 : ℝ)*(weightedGamma μ hQ (D a) (U b) ψ+weightedGamma μ hQ (D b) (U a) ψ) = _
  rw [hH,weightedLaplacianPair_symmetric μ q (D a) (D b)]
  change _ = bochnerTestForm μ hQ (-K) (H b a) ψ+weightedLaplacianPair μ q (D b) (D a)+
    (1/2 : ℝ)*(weightedGamma μ hQ (D b) (U a) ψ+weightedGamma μ hQ (D a) (U b) ψ)
  ring

end RegularPointCoordinates

end

end OAI
