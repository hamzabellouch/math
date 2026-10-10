import OAI.Geometry.SurfaceImmersion.Primitive.VelocityNormalGeometry
import OAI.Geometry.SurfaceImmersion.Primitive.LoopDensityMoments

namespace OAI

/-! Lift a normalized planar loop to the actual four-dimensional velocity
plane, retaining its exact mean, length, and leading metric. -/
noncomputable section
open scoped ContDiff Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes

/-- The fixed orthonormal-plane inclusion, written as a continuous linear map. -/
def planeLift (e₁ e₂ : Vec) : LoopDensity.Plane →L[ℝ] Vec :=
  (ContinuousLinearMap.proj 0).smulRight e₁ + (ContinuousLinearMap.proj 1).smulRight e₂

@[simp] lemma planeLift_apply (e₁ e₂ : Vec) (p : LoopDensity.Plane) :
    planeLift e₁ e₂ p = p 0 • e₁ + p 1 • e₂ := rfl

lemma planeLift_unit {e₁ e₂ : Vec} {p : LoopDensity.Plane}
    (h₁ : e₁ ⬝ᵥ e₁ = 1) (h₂ : e₂ ⬝ᵥ e₂ = 1) (horth : e₁ ⬝ᵥ e₂ = 0)
    (hp : p 0 ^ 2 + p 1 ^ 2 = 1) :
    planeLift e₁ e₂ p ⬝ᵥ planeLift e₁ e₂ p = 1 := by
  have horth' : e₂ ⬝ᵥ e₁ = 0 := (dotProduct_comm _ _).trans horth
  simp only [planeLift_apply, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, h₁, h₂, horth, horth', mul_zero, zero_add, add_zero, mul_one]
  nlinarith

lemma planeLift_perp {e₁ e₂ w : Vec} (h₁ : w ⬝ᵥ e₁ = 0) (h₂ : w ⬝ᵥ e₂ = 0)
    (p : LoopDensity.Plane) : w ⬝ᵥ planeLift e₁ e₂ p = 0 := by
  simp [planeLift_apply, dotProduct_add, dotProduct_smul, h₁, h₂]

lemma planeLift_scaled_length {e₁ e₂ : Vec} {p : LoopDensity.Plane}
    (h₁ : e₁ ⬝ᵥ e₁ = 1) (h₂ : e₂ ⬝ᵥ e₂ = 1) (horth : e₁ ⬝ᵥ e₂ = 0)
    (hp : p 0 ^ 2 + p 1 ^ 2 = 1) (R : ℝ) :
    (R • planeLift e₁ e₂ p) ⬝ᵥ (R • planeLift e₁ e₂ p) = R ^ 2 := by
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    planeLift_unit h₁ h₂ horth hp]
  ring

lemma planeLift_mean (e₁ e₂ : Vec) (R : ℝ) {p : ℝ → LoopDensity.Plane}
    (hp : Continuous p) {c : LoopDensity.Plane} (hmean : (∫ t in 0..1, p t) = c) :
    (∫ t in 0..1, R • planeLift e₁ e₂ (p t)) = R • planeLift e₁ e₂ c := by
  rw [intervalIntegral.integral_smul]
  have hi : IntervalIntegrable p MeasureTheory.volume 0 1 := hp.intervalIntegrable 0 1
  have he := (planeLift e₁ e₂).intervalIntegral_comp_comm hi
  change R • (∫ t in 0..1, (planeLift e₁ e₂) (p t)) = _
  rw [he, hmean]

/-- The real coordinate form of the leading rank-one metric identity. -/
theorem real_leading_metric {X Y C V : Vec} {a : ℝ}
    (hD : gramDet Y C ≠ 0) (hYV : Y ⬝ᵥ V = 0) (hCV : C ⬝ᵥ V = 0)
    (hR : V ⬝ᵥ V = realNormalPart Y C X ⬝ᵥ realNormalPart Y C X + a ^ 2) :
    leadingTangent X Y C V ⬝ᵥ leadingTangent X Y C V = X ⬝ᵥ X + a ^ 2 ∧
      leadingTangent X Y C V ⬝ᵥ Y = X ⬝ᵥ Y := by
  let P := realNormalPart Y C X
  have hP := realNormalPart_perp Y C X hD
  have hVP : V ⬝ᵥ P = V ⬝ᵥ X :=
    dot_normalPart_eq ((dotProduct_comm _ _).trans hYV) ((dotProduct_comm _ _).trans hCV)
  have hPP : P ⬝ᵥ P = P ⬝ᵥ X :=
    dot_normalPart_eq ((dotProduct_comm _ _).trans hP.1) ((dotProduct_comm _ _).trans hP.2)
  constructor
  · change (X - P + V) ⬝ᵥ (X - P + V) = _
    simp only [add_dotProduct, sub_dotProduct, dotProduct_add, dotProduct_sub]
    have hPV := (dotProduct_comm P V).trans hVP
    have hXP := (dotProduct_comm X P).trans hPP.symm
    have hXV := dotProduct_comm X V
    change V ⬝ᵥ V = P ⬝ᵥ P + a ^ 2 at hR
    linarith
  · change (X - P + V) ⬝ᵥ Y = _
    simp only [add_dotProduct, sub_dotProduct]
    rw [(dotProduct_comm P Y).trans hP.1, (dotProduct_comm V Y).trans hYV]
    ring

end ClosedSurfaceR4.VelocityFrame

end

end OAI
