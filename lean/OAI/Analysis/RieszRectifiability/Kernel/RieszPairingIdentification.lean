import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.NormalPairingEnergy

namespace OAI

/-!
# Scalar Riesz pairings and affine normal heights

Pairing the Riesz kernel with a fixed normal identifies its interior contribution
with the fractional bilinear form. For mean-zero tests, the exterior correction
integrates to zero, identifying the scalar Riesz pairing with the normal cutoff pairing.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

def affineNormalHeight {d : ℕ} (e z : Ambient d) (b : ℝ) (x : Ambient d) : ℝ :=
  inner ℝ e (x - z) - b

theorem affineNormalHeight_difference {d : ℕ} (e z : Ambient d) (b : ℝ) (x y : Ambient d) :
    affineNormalHeight e z b x - affineNormalHeight e z b y = inner ℝ e (x - y) := by
  rw [affineNormalHeight, affineNormalHeight, centered_coordinate_difference]
  exact normal_coordinate_difference e z x y

theorem affineNormalHeight_lipschitz {d : ℕ} (e z : Ambient d) (b : ℝ) :
    LipschitzWith ‖e‖₊ (affineNormalHeight e z b) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, affineNormalHeight_difference]
  simpa only [Real.norm_eq_abs, coe_nnnorm, dist_eq_norm] using!
    norm_inner_le_norm (𝕜 := ℝ) e (x - y)

theorem kernel_inner_normal_difference {d : ℕ} (m : ℕ) (e : Ambient d)
    (w : Ambient d → ℝ) (hw : ∀ x y, w x - w y = inner ℝ e (x - y)) (x y : Ambient d) :
    inner ℝ e (kernel m x y) = (w x - w y) * inverseDistancePow (m + 1) x y := by
  rw [kernel, real_inner_smul_right, ← hw x y, ← dist_eq_norm]
  unfold inverseDistancePow
  ring

def rieszInteriorIntegrand {d : ℕ} (m : ℕ) (e : Ambient d) (φ : Ambient d → ℝ)
    (q : Ambient d × Ambient d) : ℝ :=
  inner ℝ e (kernel m q.1 q.2) * (φ q.1 - φ q.2)

def rieszFarIntegrand {d : ℕ} (m : ℕ) (e : Ambient d) (φ : Ambient d → ℝ)
    (a : Ambient d) (q : Ambient d × Ambient d) : ℝ :=
  φ q.1 * inner ℝ e (kernel m q.1 q.2 - kernel m a q.2)

def rieszScalarPairing {d : ℕ} (m : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (R : ℝ) (e : Ambient d) (φ : Ambient d → ℝ) : ℝ :=
  let ν := μ.restrict (ball a R)
  (1 / 2 : ℝ) * (∫ q, rieszInteriorIntegrand m e φ q ∂ν.prod ν) +
    ∫ q, rieszFarIntegrand m e φ a q ∂ν.prod (μ.restrict (closedExterior a R))

theorem rieszInteriorIntegrand_eq_fractionalBilinear {d : ℕ} (m : ℕ) (e : Ambient d)
    (w φ : Ambient d → ℝ) (hw : ∀ x y, w x - w y = inner ℝ e (x - y))
    (q : Ambient d × Ambient d) :
    rieszInteriorIntegrand m e φ q = fractionalBilinear m w φ q.1 q.2 := by
  rw [rieszInteriorIntegrand, kernel_inner_normal_difference m e w hw]
  unfold inverseDistancePow fractionalBilinear
  ring

theorem rieszFarIntegrand_eq_normal_sub_correction {d : ℕ} (m : ℕ) (e : Ambient d)
    (w φ : Ambient d → ℝ) (hw : ∀ x y, w x - w y = inner ℝ e (x - y))
    (a : Ambient d) (q : Ambient d × Ambient d) :
    rieszFarIntegrand m e φ a q = renormalizedNormalIntegrand m w φ a q -
      (φ q.1 * w a) * inverseDistancePow (m + 1) a q.2 := by
  rw [rieszFarIntegrand, inner_sub_right, kernel_inner_normal_difference m e w hw,
    kernel_inner_normal_difference m e w hw]
  unfold renormalizedNormalIntegrand
  ring

theorem riesz_far_integral_eq_normal {d : ℕ} (m : ℕ) (C : ℝ)
    (μ ν : Measure (Ambient d)) [SFinite μ] [IsFiniteMeasure ν]
    (hg : GlobalUpperGrowth m C μ) (e : Ambient d) (w φ : Ambient d → ℝ)
    (hw : ∀ x y, w x - w y = inner ℝ e (x - y))
    (a : Ambient d) (R : ℝ) (hR : 0 < R) (hφ : Integrable φ ν) (hzero : (∫ x, φ x ∂ν) = 0)
    (hN : Integrable (renormalizedNormalIntegrand m w φ a) (ν.prod (μ.restrict (closedExterior a R)))) :
    Integrable (rieszFarIntegrand m e φ a) (ν.prod (μ.restrict (closedExterior a R))) ∧
      (∫ q, rieszFarIntegrand m e φ a q ∂ν.prod (μ.restrict (closedExterior a R))) =
        ∫ q, renormalizedNormalIntegrand m w φ a q ∂ν.prod (μ.restrict (closedExterior a R)) := by
  have hk := (inverseDistancePow_closedExterior_integrable_and_bound m C μ hg a R hR).1
  have hcorrection := (hφ.mul_const (w a)).mul_prod hk
  have heq : rieszFarIntegrand m e φ a = fun q => renormalizedNormalIntegrand m w φ a q -
      (φ q.1 * w a) * inverseDistancePow (m + 1) a q.2 := by
    funext q
    exact rieszFarIntegrand_eq_normal_sub_correction m e w φ hw a q
  rw [heq]
  refine ⟨hN.sub hcorrection, ?_⟩
  rw [integral_sub hN hcorrection, integral_prod_mul (fun x => φ x * w a) (inverseDistancePow (m + 1) a),
    integral_mul_const, hzero, zero_mul, zero_mul, sub_zero]

theorem normalCutoffPairing_eq_rieszScalarPairing {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hg : GlobalUpperGrowth m C μ)
    (e : Ambient d) (w χ : Ambient d → ℝ)
    (hw : ∀ x y, w x - w y = inner ℝ e (x - y))
    (a : Ambient d) (R : ℝ) (hR : 0 < R)
    (hφ : Integrable (fun x => χ x ^ 2 * w x) (μ.restrict (ball a R)))
    (hzero : (∫ x in ball a R, χ x ^ 2 * w x ∂μ) = 0)
    (hN : Integrable (renormalizedNormalIntegrand m w (fun x => χ x ^ 2 * w x) a)
      ((μ.restrict (ball a R)).prod (μ.restrict (closedExterior a R)))) :
    normalCutoffPairing m μ a R w χ = rieszScalarPairing m μ a R e (fun x => χ x ^ 2 * w x) := by
  have := finiteMeasure_restrict_ball_of_globalGrowth m C μ hg a R hR
  have hext := (riesz_far_integral_eq_normal m C μ (μ.restrict (ball a R)) hg e w
    (fun x => χ x ^ 2 * w x) hw a R hR hφ hzero hN).2
  unfold normalCutoffPairing rieszScalarPairing
  simp_rw [rieszInteriorIntegrand_eq_fractionalBilinear m e w _ hw]
  rw [hext]

end

end RieszRectifiability

end OAI
