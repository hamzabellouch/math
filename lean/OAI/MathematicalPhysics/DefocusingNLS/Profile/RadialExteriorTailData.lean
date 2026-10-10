import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorBoundedExpansion
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorUnweight

namespace OAI

/-! Bounded polynomial residual data and decay after removing the exterior weight. -/

open Set Filter Polynomial
open scoped BoundedContinuousFunction
namespace DefocusingNLS

noncomputable def boundedRadialResidual (P : ℂ[X]) : ℝ →ᵇ ℂ × ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t => (0,-boundedRadialPolynomial P t))
    (continuous_const.prodMk (boundedRadialPolynomial P).continuous.neg)
    ‖boundedRadialPolynomial P‖ (fun t => by
      simp only [Prod.norm_def,norm_zero,norm_neg,max_eq_right (norm_nonneg _)]
      exact (boundedRadialPolynomial P).norm_coe_le_norm t)

theorem boundedRadialResidual_apply (P : ℂ[X]) (t : ℝ) :
    boundedRadialResidual P t=(0,-boundedRadialPolynomial P t) := rfl

theorem radialExteriorUnweight_tendsto (κ : ℝ) (hκ : 0 < κ) (v : ℝ →ᵇ ℂ × ℂ) :
    Tendsto (radialExteriorUnweight κ v) atTop (nhds 0) := by
  have he : Tendsto (fun t : ℝ => Real.exp (-κ*t)) atTop (nhds 0) := by
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop hκ) using 1
    funext t
    simp [neg_mul]
  have hb := he.mul_const ‖v‖
  simp only [zero_mul] at hb
  apply squeeze_zero_norm' _ hb
  exact Eventually.of_forall (fun t => radialExteriorUnweight_norm κ t v ‖v‖ (v.norm_coe_le_norm t))

theorem radialExterior_normalized_residual (ν : ℂ) (n : ℕ) (m : ℂ) (j : ℕ) :
    ∃ R : ℂ[X], ∀ t : ℝ, 0 ≤ t →
      Real.exp (-(2*(j : ℝ))*t) • boundedRadialResidual R t =
        (0,-radialExteriorPolynomialFunction
          (radialExteriorPolynomialResidual ν n (radialExteriorExpansion ν n m j)) t) := by
  obtain ⟨R,hR⟩ := radialExteriorPolynomialResidual_factor ν n m j
  refine ⟨R,?_⟩
  intro t ht
  rw [hR t,boundedRadialResidual_apply,boundedRadialPolynomial_nonneg R t ht]
  apply Prod.ext
  · simp
  · simp [Complex.real_smul]

end DefocusingNLS

end OAI
