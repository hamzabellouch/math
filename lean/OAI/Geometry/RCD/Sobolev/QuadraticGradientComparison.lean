import OAI.Geometry.RCD.Sobolev.QuadraticCutoffIdentity
import OAI.Geometry.RCD.Harmonic.QuadraticGramError

namespace OAI

/-! # The exact cutoff energy identity for the distance-model difference -/

open Set MeasureTheory
open scoped NNReal BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [ProperSpace X] in
private theorem weighted_gamma_integrable (c f g : SobolevSpace μ hQ) (C : ℝ≥0)
    (hc : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ c x| ≤ C) :
    Integrable (fun x => SobolevSpace.toLp μ hQ c x * localGamma μ hQ f g x) μ :=
  (localGamma_memL1 μ hQ f g).bdd_mul (Lp.aestronglyMeasurable (SobolevSpace.toLp μ hQ c))
    (by simpa only [Real.norm_eq_abs] using hc)

private theorem gamma_sub_right (a b d : SobolevSpace μ hQ) :
    localGamma μ hQ a (b - d) =ᵐ[μ]
      fun x => localGamma μ hQ a b x - localGamma μ hQ a d x := by
  filter_upwards [localGamma_comm μ hQ a (b - d), localGamma_sub_left μ hQ b d a,
    localGamma_comm μ hQ b a, localGamma_comm μ hQ d a] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]

/-- Polarization keeps the signed cross term until after integration. -/
theorem weighted_difference_energy (c q H : SobolevSpace μ hQ) (C : ℝ≥0)
    (hc : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ c x| ≤ C) :
    (∫ x, SobolevSpace.toLp μ hQ c x * localGamma μ hQ (q - H) (q - H) x ∂μ) =
      (∫ x, SobolevSpace.toLp μ hQ c x * localGamma μ hQ q q x ∂μ) -
      (∫ x, SobolevSpace.toLp μ hQ c x * localGamma μ hQ H H x ∂μ) -
      2 * ∫ x, SobolevSpace.toLp μ hQ c x * localGamma μ hQ (q - H) H x ∂μ := by
  have hp : (fun x => SobolevSpace.toLp μ hQ c x * localGamma μ hQ (q - H) (q - H) x) =ᵐ[μ]
      fun x => SobolevSpace.toLp μ hQ c x * localGamma μ hQ q q x -
        SobolevSpace.toLp μ hQ c x * localGamma μ hQ H H x -
        2 * (SobolevSpace.toLp μ hQ c x * localGamma μ hQ (q - H) H x) := by
    filter_upwards [localGamma_sub_left μ hQ q H (q - H),
      gamma_sub_right μ hQ q q H, gamma_sub_right μ hQ H q H,
      localGamma_sub_left μ hQ q H H, localGamma_comm μ hQ H q] with x h₁ h₂ h₃ h₄ hsym
    rw [h₁, h₂, h₃, h₄, hsym]
    ring
  rw [integral_congr_ae hp]
  calc
    _ = (∫ x, SobolevSpace.toLp μ hQ c x * localGamma μ hQ q q x -
        SobolevSpace.toLp μ hQ c x * localGamma μ hQ H H x ∂μ) -
        ∫ x, 2 * (SobolevSpace.toLp μ hQ c x * localGamma μ hQ (q - H) H x) ∂μ :=
      integral_sub ((weighted_gamma_integrable μ hQ c q q C hc).sub
      (weighted_gamma_integrable μ hQ c H H C hc))
      ((weighted_gamma_integrable μ hQ c (q - H) H C hc).const_mul 2)
    _ = _ := by rw [integral_sub (weighted_gamma_integrable μ hQ c q q C hc)
      (weighted_gamma_integrable μ hQ c H H C hc), integral_const_mul]

/-- The gradient error between squared distance and the quadratic
coordinate model is expressed using value errors and the actual Gram
trace. This is the integration-by-parts step in qualitative convergence. -/
theorem coordinateQuadratic_difference_energy {n : ℕ} {Ω : Set X}
    (u : Fin n → SobolevSpace μ hQ) (C D E L : ℝ≥0)
    (hu : ∀ j, IsSobolevHarmonicOn μ hQ Ω (u j))
    (hub : ∀ j, ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (u j) x| ≤ C)
    (c q : SobolevSpace μ hQ) (χ : X → ℝ)
    (hχ : LipschitzWith L χ) (hcpt : HasCompactSupport χ)
    (hbound : ∀ x, |χ x| ≤ E) (hnonneg : ∀ x, 0 ≤ χ x)
    (hsupp : tsupport χ ⊆ Ω) (hcrep : SobolevSpace.toLp μ hQ c =ᵐ[μ] χ)
    (hw : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (q - coordinateQuadratic μ hQ u C) x| ≤ D) :
    let H := coordinateQuadratic μ hQ u C
    let w := q - H
    (∫ x, SobolevSpace.toLp μ hQ c x * localGamma μ hQ w w x ∂μ) =
      (∫ x, SobolevSpace.toLp μ hQ c x * localGamma μ hQ q q x ∂μ) -
      (∫ x, SobolevSpace.toLp μ hQ c x * localGamma μ hQ H H x ∂μ) +
      2 * (∫ x, SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ c w E D) x *
        (∑ j, localGamma μ hQ (u j) (u j) x) ∂μ) +
      2 * ∫ x, SobolevSpace.toLp μ hQ w x * localGamma μ hQ c H x ∂μ := by
  have hc : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ c x| ≤ E := by
    filter_upwards [hcrep] with x hx
    rw [hx]
    exact hbound x
  have hid := weighted_difference_energy μ hQ c q (coordinateQuadratic μ hQ u C) E hc
  have hcross := coordinateQuadratic_cutoff_cross μ hQ u C D E L hu hub
    c (q - coordinateQuadratic μ hQ u C) χ hχ hcpt hbound hnonneg hsupp hcrep hw
  rw [hcross] at hid
  dsimp only
  linarith

end RegularPointCoordinates

end

end OAI
