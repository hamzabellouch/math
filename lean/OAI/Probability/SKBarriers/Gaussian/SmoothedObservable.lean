import Mathlib
import OAI.Probability.SKBarriers.Gaussian.BoundedPrimitive
import OAI.Probability.SKBarriers.Scalar.ScalarHierarchyAverageAlgebra

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def scalarWindow (g : ℝ → ℝ) (h x : ℝ) : ℝ :=
  (boundedPrimitive g (x+h)-boundedPrimitive g x)/h

def scalarWindowDerivative (g : ℝ → ℝ) (h x : ℝ) : ℝ := (g (x+h)-g x)/h

theorem scalarWindow_hasDerivAt {g : ℝ → ℝ} (hg : Continuous g) (h x : ℝ) :
    HasDerivAt (scalarWindow g h) (scalarWindowDerivative g h x) x := by
  convert (((boundedPrimitive_hasDerivAt hg (x+h)).comp x
    ((hasDerivAt_id x).add_const h)).sub (boundedPrimitive_hasDerivAt hg x)).div_const h using 1 <;>
    first | rfl | exact Subsingleton.elim _ _ | simp only [scalarWindowDerivative,mul_one]

theorem scalarWindowDerivative_continuous {g : ℝ → ℝ} (hg : Continuous g) (h : ℝ) :
    Continuous (scalarWindowDerivative g h) :=
  ((hg.comp (continuous_id.add continuous_const)).sub hg).div_const h

theorem scalarWindow_bound {g : ℝ → ℝ} (hg : Continuous g) {B : ℝ≥0}
    (hB : ∀ x, |g x| ≤ B) {h : ℝ} (hh : 0<h) (x : ℝ) :
    |scalarWindow g h x| ≤ B := by
  have H := (boundedPrimitive_lipschitz hg hB).dist_le_mul (x+h) x
  simp only [Real.dist_eq,add_sub_cancel_left,abs_of_pos hh] at H
  rw [scalarWindow,abs_div,abs_of_pos hh,div_le_iff₀ hh]
  exact H

theorem scalarWindowDerivative_bound {g : ℝ → ℝ} {B : ℝ≥0}
    (hB : ∀ x, |g x| ≤ B) {h : ℝ} (hh : 0<h) (x : ℝ) :
    |scalarWindowDerivative g h x| ≤ 2*(B:ℝ)/h := by
  rw [scalarWindowDerivative,abs_div,abs_of_pos hh]
  exact div_le_div_of_nonneg_right ((abs_sub (g (x+h)) (g x)).trans (by linarith [hB (x+h),hB x])) hh.le

theorem scalarWindow_integral {g : ℝ → ℝ} (hg : Continuous g) (h x : ℝ) :
    scalarWindow g h x=(∫ y in x..x+h, g y)/h := by
  have H := intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (μ:=volume) 0 x) (hg.intervalIntegrable (μ:=volume) x (x+h))
  dsimp only [scalarWindow,boundedPrimitive]
  congr 1
  linarith

theorem scalarWindow_approx {g : ℝ → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    {h : ℝ} (hh : 0<h) (x : ℝ) : |scalarWindow g h x-g x| ≤ (L:ℝ)*h := by
  rw [scalarWindow_integral hg.continuous]
  have H := intervalIntegral.norm_integral_le_of_norm_le_const (a:=x) (b:=x+h)
    (f:=fun y => g y-g x) (C:=(L:ℝ)*h) (by
      intro y hy
      rw [uIoc_of_le (by linarith)] at hy
      have H := hg.dist_le_mul y x
      simp only [Real.dist_eq] at H
      rw [abs_of_nonneg (show 0≤y-x by linarith [hy.1])] at H
      rw [Real.norm_eq_abs]
      exact H.trans (mul_le_mul_of_nonneg_left (by linarith [hy.2]) L.coe_nonneg))
  rw [intervalIntegral.integral_sub (hg.continuous.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
    intervalIntegral.integral_const,smul_eq_mul,add_sub_cancel_left,Real.norm_eq_abs,
    abs_of_pos hh] at H
  rw [show (∫ y in x..x+h, g y)/h-g x=((∫ y in x..x+h, g y)-h*g x)/h by field_simp,
    abs_div,abs_of_pos hh,div_le_iff₀ hh]
  exact H

theorem scalarHierarchyAverage_observable_distance {f g a : ℝ → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedScalar g) (ha : BoundedScalar a)
    {δ : ℝ} (_hδ : 0≤δ) (hga : ∀ z, |g z-a z| ≤ δ)
    (n : ℕ) (m v : Fin n → ℝ) (x : ℝ) :
    |scalarHierarchyAverage n m v f g x-scalarHierarchyAverage n m v f a x| ≤ δ := by
  rw [← scalarHierarchyAverage_sub hf hg ha,
    scalarHierarchyAverage_integral hf (hg.sub ha)]
  have : IsProbabilityMeasure (hierarchyPathLaw n m (fun z => f (x+coordinateLinear n v z)) 0) :=
    hierarchyPathLaw_probability n m _ ((hf.translate x).compCLM (coordinateLinear n v)) 0
  have H := norm_integral_le_of_norm_le_const (μ:=hierarchyPathLaw n m
    (fun z => f (x+coordinateLinear n v z)) 0) (f:=fun z => g (x+coordinateLinear n v z)-a (x+coordinateLinear n v z))
    (C:=δ) (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hga (x+coordinateLinear n v z)))
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using H

end SK.Analytic

end
end

end OAI
