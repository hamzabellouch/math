import OAI.Geometry.RCD.Heat.KernelHeatL2Representation

namespace OAI

/-! # Pointwise order and linearity of L2 kernel heat -/

open MeasureTheory
open scoped InnerProductSpace
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {p : ℝ → X → X → ℝ} (hp : IsContinuousHeatKernel μ hQ p)

theorem kernelHeat_sub (t : ℝ) (f g : Lp ℝ 2 μ) (x : X) :
    kernelHeat μ hQ hp t (f-g) x = kernelHeat μ hQ hp t f x-kernelHeat μ hQ hp t g x := by
  exact inner_sub_right _ _ _

theorem kernelHeat_smul (t c : ℝ) (f : Lp ℝ 2 μ) (x : X) :
    kernelHeat μ hQ hp t (c • f) x = c*kernelHeat μ hQ hp t f x := by
  exact real_inner_smul_right _ _ _

theorem kernelHeat_mono {t : ℝ} (ht : 0 < t) {f g : Lp ℝ 2 μ} (hfg : f ≤ g) (x : X) :
    kernelHeat μ hQ hp t f x ≤ kernelHeat μ hQ hp t g x := by
  rw [kernelHeat_eq_integral μ hQ hp ht,kernelHeat_eq_integral μ hQ hp ht]
  apply integral_mono_ae ((heatKernel_memLp μ hQ hp ht x).integrable_mul (Lp.memLp f))
    ((heatKernel_memLp μ hQ hp ht x).integrable_mul (Lp.memLp g))
  filter_upwards [(Lp.coeFn_le _ _).mpr hfg] with y hy
  exact mul_le_mul_of_nonneg_left hy (hp.nonneg t ht x y)

end RegularPointCoordinates

end

end OAI
