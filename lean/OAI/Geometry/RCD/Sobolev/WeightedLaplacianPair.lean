import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # A symmetric weighted pairing of L² Laplacians -/

open MeasureTheory
open scoped NNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X)

def weightedLaplacianPair (v : X →ᵇ ℝ) : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ →ₗ[ℝ] ℝ :=
  let T := lpMultiplier μ (boundedMultiplier μ v v.continuous.measurable ‖v‖₊
    (fun x => v.norm_coe_le_norm x))
  LinearMap.mk₂ ℝ (fun d e => inner ℝ d (T e))
    (by intro d e f; exact inner_add_left _ _ _)
    (by intro c d e; simp only [real_inner_smul_left,smul_eq_mul])
    (by intro d e f; rw [map_add,inner_add_right])
    (by intro c d e; simp only [map_smul,real_inner_smul_right,smul_eq_mul])

theorem weightedLaplacianPair_apply (v : X →ᵇ ℝ) (d e : Lp ℝ 2 μ) :
    weightedLaplacianPair μ v d e = ∫ x, v x*d x*e x ∂μ := by
  change inner ℝ d (lpMultiplier μ (boundedMultiplier μ v v.continuous.measurable ‖v‖₊
    (fun x => v.norm_coe_le_norm x)) e) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [lpMultiplier_coe μ (boundedMultiplier μ v v.continuous.measurable ‖v‖₊
    (fun x => v.norm_coe_le_norm x)) e,
    boundedMultiplier_coe μ v v.continuous.measurable ‖v‖₊ (fun x => v.norm_coe_le_norm x)] with x hx hv
  simp only [Real.inner_apply,hx,hv]
  ring

theorem weightedLaplacianPair_symmetric (v : X →ᵇ ℝ) (d e : Lp ℝ 2 μ) :
    weightedLaplacianPair μ v d e = weightedLaplacianPair μ v e d := by
  rw [weightedLaplacianPair_apply,weightedLaplacianPair_apply]
  congr 1
  funext x
  ring

theorem weightedLaplacianPair_nonneg (v : X →ᵇ ℝ) (hv : 0≤v) (d : Lp ℝ 2 μ) :
    0≤weightedLaplacianPair μ v d d := by
  rw [weightedLaplacianPair_apply]
  apply integral_nonneg
  intro x
  change 0 ≤ v x*d x*d x
  calc
    0 ≤ v x*(d x)^2 := mul_nonneg (hv x) (sq_nonneg (d x))
    _ = _ := by ring

end RegularPointCoordinates

end

end OAI
