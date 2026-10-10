import OAI.Geometry.RCD.Heat.HeatOverlapKernel

namespace OAI

/-! # The canonical symmetric heat-kernel candidate

The half-time overlap fixes one symmetric representative at all points,
with measurability, mass conservation and semigroup representation.
Continuity and finiteness of the underlying extended overlap are not presumed.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

def canonicalHeatKernel (t : ℝ) (x y : X) : ℝ :=
  if ht : 0 < t then (hX.heatOverlapKernel hn p (t / 2) (half_pos ht) x y).toReal else 0

omit [SeparableSpace X] [IsLocallyFiniteMeasure (hausdorff n X)] in
theorem canonicalHeatKernel_nonneg (t : ℝ) (x y : X) :
    0 ≤ hX.canonicalHeatKernel hn p t x y := by
  unfold canonicalHeatKernel
  split_ifs <;> positivity

omit [SeparableSpace X] [IsLocallyFiniteMeasure (hausdorff n X)] in
theorem canonicalHeatKernel_symmetric (t : ℝ) (x y : X) :
    hX.canonicalHeatKernel hn p t x y = hX.canonicalHeatKernel hn p t y x := by
  unfold canonicalHeatKernel
  split_ifs
  · rw [hX.heatOverlapKernel_symmetric hn p]
  · rfl

theorem canonicalHeatKernel_measurable (t : ℝ) :
    Measurable (fun xy : X × X => hX.canonicalHeatKernel hn p t xy.1 xy.2) := by
  by_cases ht : 0 < t
  · simpa only [canonicalHeatKernel, dite_eq_left ht] using
      (hX.heatOverlapKernel_lowerSemicontinuous hn p (t / 2) (half_pos ht)).measurable.ennreal_toReal
  · simp only [canonicalHeatKernel, dite_eq_right ht]
    exact measurable_const

theorem canonicalHeatKernel_ae (t : ℝ) (ht : 0 < t) (x : X) :
    hX.canonicalHeatKernel hn p t x =ᵐ[hausdorff n X] hX.heatJointDensity hn p t ht x := by
  have H : hX.heatOverlapKernel hn p (t / 2) (half_pos ht) x =ᵐ[hausdorff n X]
      fun y => ENNReal.ofReal (hX.heatJointDensity hn p t ht x y) := by
    simpa only [add_halves] using! hX.heatOverlapKernel_ae hn p (t / 2) (half_pos ht) x
  filter_upwards [H] with y hy
  simp only [canonicalHeatKernel, dite_eq_left ht, hy,
    ENNReal.toReal_ofReal (hX.heatJointDensity_nonneg hn p t ht x y)]

theorem canonicalHeatKernel_integrable (t : ℝ) (ht : 0 < t) (x : X) :
    Integrable (hX.canonicalHeatKernel hn p t x) (hausdorff n X) :=
  (hX.heatJointDensity_integrable hn p t ht x).congr (hX.canonicalHeatKernel_ae hn p t ht x).symm

theorem canonicalHeatKernel_mass_one (t : ℝ) (ht : 0 < t) (x : X) :
    (∫ y, hX.canonicalHeatKernel hn p t x y ∂hausdorff n X) = 1 := by
  rw [integral_congr_ae (hX.canonicalHeatKernel_ae hn p t ht x)]
  exact hX.heatJointDensity_mass_one hn p t ht x

theorem canonicalHeatKernel_represents (t : ℝ) (ht : 0 < t)
    (f : Lp ℝ 2 (hausdorff n X)) (hf : Integrable f (hausdorff n X)) :
    (fun x => ∫ y, hX.canonicalHeatKernel hn p t x y * f y ∂hausdorff n X) =ᵐ[hausdorff n X]
      heatAt (hausdorff n X) hX.quadratic t f := by
  filter_upwards [hX.heatJointDensity_represents hn p t ht f hf] with x hx
  calc
    _ = ∫ y, hX.heatJointDensity hn p t ht x y * f y ∂hausdorff n X := by
      apply integral_congr_ae
      filter_upwards [hX.canonicalHeatKernel_ae hn p t ht x] with y hy
      rw [hy]
    _ = _ := hx

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
