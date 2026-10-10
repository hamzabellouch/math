import OAI.Geometry.RCD.Sobolev.LogDensityGradient

namespace OAI

/-! # Fisher-energy finiteness from the actual log-density gradient bound -/

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 theorem renyi_fisher_pointwise {r b L q : ℝ} (hr : 0 < r) (hb : 0 ≤ b)
    (hL : b ≤ L*r) : r^(2*q-3)*b^2 ≤ L^2*r^(2*q-1) := by
  have hsq : b^2 ≤ (L*r)^2 := pow_le_pow_left₀ hb hL 2
  calc
    _ ≤ r^(2*q-3)*(L*r)^2 := mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hr.le _)
    _ = L^2*(r^(2*q-3)*r^2) := by ring
    _ = L^2*(r^(2*q-3)*r^(2:ℝ)) := by rw [Real.rpow_two]
    _ = _ := by rw [←Real.rpow_add hr]; congr 2; ring

 theorem SobolevSpace.renyi_fisher_of_log_lipschitz (ρ : SobolevSpace μ hQ)
    (hp : ∀ᵐ x ∂μ, 0 < SobolevSpace.toLp μ hQ ρ x)
    {g : X → ℝ} {L M : ℝ≥0} (hg : LipschitzWith L g)
    (hlog : (fun x => Real.log (SobolevSpace.toLp μ hQ ρ x)) =ᵐ[μ] g)
    (hM : ∀ x, Real.exp (g x) ≤ M) (q : ℝ)
    (hi : Integrable (fun x => (SobolevSpace.toLp μ hQ ρ x)^(2*q-1)) μ) :
    Integrable (fun x => (SobolevSpace.toLp μ hQ ρ x)^(2*q-3)*
      (SobolevSpace.minimalSlope μ hQ ρ x)^2) μ ∧
    (∫ x, (SobolevSpace.toLp μ hQ ρ x)^(2*q-3)*
      (SobolevSpace.minimalSlope μ hQ ρ x)^2 ∂μ) ≤
      (L:ℝ)^2*(∫ x, (SobolevSpace.toLp μ hQ ρ x)^(2*q-1) ∂μ) := by
  have hrep : SobolevSpace.toLp μ hQ ρ =ᵐ[μ] fun x => Real.exp (g x) := by
    filter_upwards [hp,hlog] with x hx hl
    rw [←hl,Real.exp_log hx]
  have hgrad := ρ.relative_gradient_of_log_lipschitz μ hQ hg hM hrep
  have hb : ∀ᵐ x ∂μ, (SobolevSpace.toLp μ hQ ρ x)^(2*q-3)*
      (SobolevSpace.minimalSlope μ hQ ρ x)^2 ≤ (L:ℝ)^2*
        (SobolevSpace.toLp μ hQ ρ x)^(2*q-1) := by
    filter_upwards [hp,hgrad,(Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ ρ)]
      with x hx hgx hbx
    exact renyi_fisher_pointwise hx hbx hgx
  have hn : ∀ᵐ x ∂μ, 0 ≤ (SobolevSpace.toLp μ hQ ρ x)^(2*q-3)*
      (SobolevSpace.minimalSlope μ hQ ρ x)^2 :=
    hp.mono fun x hx => mul_nonneg (Real.rpow_nonneg hx.le _) (sq_nonneg _)
  have hm : Measurable (fun x => (SobolevSpace.toLp μ hQ ρ x)^(2*q-3)*
      (SobolevSpace.minimalSlope μ hQ ρ x)^2) :=
    ((Lp.stronglyMeasurable _).measurable.pow_const _).mul
      ((Lp.stronglyMeasurable _).measurable.pow_const 2)
  have hfi := (hi.const_mul ((L:ℝ)^2)).mono_nonneg hm.aestronglyMeasurable hn hb
  refine ⟨hfi,?_⟩
  rw [←integral_const_mul]
  exact integral_mono_ae hfi (hi.const_mul _) hb

end RegularPointCoordinates

end

end OAI
