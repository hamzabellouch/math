import OAI.Geometry.RCD.Sobolev.ProjectedEulerIdentity
import OAI.Geometry.RCD.Transport.ScaledRadialTransport

namespace OAI

/-! # Small-radius transport for the actual Sobolev forcing -/

open Set Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

omit [IsFiniteMeasureOnCompacts μ] in
/-- Convert the exact local L2 identity into the scalar equation used by
the weak divergence test. -/
theorem scaled_radial_derivative_add_representative (Ω : Set X)
    (f w q : SobolevSpace μ hQ) {B : ℝ}
    (hf : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ f f x ≤ B)
    (heq : localRadialDerivative μ hQ Ω f hf w = SobolevSpace.restrictLp μ hQ Ω (w + q)) :
    localGamma μ hQ f w =ᵐ[μ.restrict Ω]
      fun x => SobolevSpace.toLp μ hQ w x + SobolevSpace.toLp μ hQ q x := by
  have hd := localRadialDerivative_representative μ hQ Ω f w hf
  rw [heq] at hd
  have he := hd.symm.trans (SobolevSpace.restrictLp_coe μ hQ Ω (w + q))
  rw [map_add] at he
  exact he.trans (ae_restrict_of_ae (Lp.coeFn_add _ _))

/-- The forcing in the projected Euler equation is a
Sobolev function. Its square enters the outer bound with a quadratic
coefficient, so the residual can later be normalized safely. -/
theorem scaled_radial_transport_sobolev_forcing {n : ℕ} {R a : ℝ} (hR : 0 < R)
    (ha : 0 ≤ a) (han : a ≤ (n : ℝ) + 1) (z : X)
    (f w q : SobolevSpace μ hQ)
    (hlap : IsConstantLaplacianOn μ hQ (ball z (4 * R)) f a)
    {B : ℝ} (hf : ∀ᵐ x ∂μ.restrict (ball z (4 * R)), localGamma μ hQ f f x ≤ B)
    (C : ℝ≥0) (hw : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ w x| ≤ C)
    (e : X → ℝ) (he : MemLp e 2 μ)
    (heuler : localRadialDerivative μ hQ (ball z (4 * R)) f hf w =
      SobolevSpace.restrictLp μ hQ (ball z (4 * R)) (w + q))
    (hradial : localGamma μ hQ f (inwardSobolev μ hQ z (3 * R))
      =ᵐ[μ.restrict (ball z (3 * R))] fun x => e x - dist z x)
    (hsphere : μ (sphere z R) = 0) :
    let β := transportCutoffExponent n
    let D := (R ^ (-β) - (3 * R) ^ (-β)) / β
    let Q := R ^ (-(β + 1))
    let m := (R / 2) * (2 * R) ^ (-(β + 1))
    (∫ x in ball z (2 * R), (SobolevSpace.toLp μ hQ w x) ^ 2 ∂μ) ≤
      (1 + 2 * ((a + 2) * D + D / 4) / m) *
        (∫ x in ball z R, (SobolevSpace.toLp μ hQ w x) ^ 2 ∂μ) +
      (8 * D / m) * (∫ x in ball z (4 * R), (SobolevSpace.toLp μ hQ q x) ^ 2 ∂μ) +
      (4 * (C : ℝ) ^ 2 * Q / (R * m)) * (∫ x in ball z (4 * R), (e x) ^ 2 ∂μ) := by
  have hF : MemLp (fun x => 2 * SobolevSpace.toLp μ hQ q x) 2 μ :=
    (Lp.memLp (SobolevSpace.toLp μ hQ q)).const_mul 2
  have hEq : localGamma μ hQ f w =ᵐ[μ.restrict (ball z (4 * R))]
      fun x => SobolevSpace.toLp μ hQ w x + (2 * SobolevSpace.toLp μ hQ q x) / 2 := by
    filter_upwards [scaled_radial_derivative_add_representative μ hQ _ f w q hf heuler] with x hx
    rw [hx]
    ring
  have ht := scaled_radial_transport_squared μ hQ hR ha han z f w hlap C hw
    (fun x => 2 * SobolevSpace.toLp μ hQ q x) e hF he hEq hradial hsphere
  dsimp only at ht ⊢
  have hsq : (fun x => (2 * SobolevSpace.toLp μ hQ q x) ^ 2) =
      fun x => (4 : ℝ) * (SobolevSpace.toLp μ hQ q x) ^ 2 := by funext x; ring
  rw [hsq, integral_const_mul] at ht
  convert ht using 1
  ring

end RegularPointCoordinates

end

end OAI
