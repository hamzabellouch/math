import OAI.Geometry.RCD.Heat.HeatSmoothingScale
import OAI.Geometry.RCD.Sobolev.SqrtDerivativeBound

namespace OAI

/-! # Time variation of averages for a weak Poisson solution -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

omit [MetricSpace X] [BorelSpace X] [ProperSpace X] [μ.Regular] in
/-- A finite-set average is a continuous linear functional on L². -/
theorem lp_setAverage_eq_inner (A : Set X) (hA : MeasurableSet A) (hAt : μ A ≠ ∞)
    (f : Lp ℝ 2 μ) :
    (⨍ x in A, f x ∂μ) =
      (μ.real A)⁻¹ * inner ℝ (indicatorConstLp 2 hA hAt (1:ℝ)) f := by
  rw [L2.inner_indicatorConstLp_one,average_eq,measureReal_restrict_apply_univ,smul_eq_mul]

theorem heat_setAverage_continuous (A : Set X) (hA : MeasurableSet A) (hAt : μ A ≠ ∞)
    (f : Lp ℝ 2 μ) : Continuous (fun t => ⨍ x in A, heatAt μ hQ t f x ∂μ) := by
  simp_rw [lp_setAverage_eq_inner μ A hA hAt]
  exact continuous_const.mul (continuous_const.inner (heatAt_continuous μ hQ f))

theorem heat_setAverage_add (A : Set X) (hA : MeasurableSet A) (hAt : μ A ≠ ∞)
    (t : ℝ) (f g : Lp ℝ 2 μ) :
    (⨍ x in A, heatAt μ hQ t (f+g) x ∂μ) =
      (⨍ x in A, heatAt μ hQ t f x ∂μ)+(⨍ x in A, heatAt μ hQ t g x ∂μ) := by
  simp only [lp_setAverage_eq_inner μ A hA hAt,map_add,inner_add_right,mul_add]

/-- The weak Laplacian gives the genuine derivative of every finite-set
average, including for initial data with no chosen pointwise representative. -/
theorem heat_weakLaplacian_average_hasDerivAt
    (u : SobolevSpace μ hQ) (d : Lp ℝ 2 μ) (hd : IsWeakLaplacian μ hQ u d)
    (A : Set X) (hA : MeasurableSet A) (hAt : μ A ≠ ∞) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ⨍ x in A, heatAt μ hQ s (SobolevSpace.toLp μ hQ u) x ∂μ)
      (⨍ x in A, heatAt μ hQ t d x ∂μ) t := by
  simp_rw [lp_setAverage_eq_inner μ A hA hAt]
  have hh := ((hasDerivAt_const t (indicatorConstLp 2 hA hAt (1:ℝ))).inner ℝ
    (heat_weakLaplacian_hasDerivAt μ hQ u d hd ht)).const_mul ((μ.real A)⁻¹)
  simpa only [inner_zero_left,add_zero] using hh

end RegularPointCoordinates

end

end OAI
