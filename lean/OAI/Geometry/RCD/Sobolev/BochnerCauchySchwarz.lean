import OAI.Geometry.RCD.Coordinates.RegularBochnerPositivity

namespace OAI

/-! # Cauchy--Schwarz for the full polarized Bochner expression -/

open Set Filter MeasureTheory
open scoped NNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ) {m : ℕ}

theorem regularBochnerForm_cauchySchwarz (K : ℝ)
    (U : Euclidean m →L[ℝ] SobolevSpace μ hQ) (D : Euclidean m →L[ℝ] Lp ℝ 2 μ)
    (H : Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] SobolevSpace μ hQ)
    (q : X →ᵇ ℝ) (ψ : SobolevSpace μ hQ) (L : Euclidean m → ℝ≥0)
    (hU : ∀ a, ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ (U a) x≤L a)
    (hH : ∀ a b, H a b=H b a)
    (hpos : ∀ a, 0≤regularBochnerForm μ hQ K U D H q ψ L hU a a)
    (a b : Euclidean m) :
    (regularBochnerForm μ hQ K U D H q ψ L hU a b)^2 ≤
      regularBochnerForm μ hQ K U D H q ψ L hU a a *
        regularBochnerForm μ hQ K U D H q ψ L hU b b := by
  let B := regularBochnerForm μ hQ K U D H q ψ L hU
  have hba : B b a=B a b := regularBochnerForm_symmetric μ hQ K U D H q ψ L hU hH b a
  have hquad (t : ℝ) : 0≤B b b*(t*t)+(2*B a b)*t+B a a := by
    have ht := hpos (a+t • b)
    change 0≤B (a+t • b) (a+t • b) at ht
    simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul] at ht
    rw [hba] at ht
    nlinarith only [ht]
  have hd := discrim_le_zero hquad
  simp only [discrim] at hd
  change (B a b)^2≤B a a*B b b
  nlinarith only [hd]

end RegularPointCoordinates

end

end OAI
