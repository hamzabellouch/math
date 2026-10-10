import OAI.Geometry.RCD.Heat.CappedIntegralProduct

namespace OAI

/-! # Continuous bounded approximations to the heat overlap kernel -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

/-- The overlap of two density rows after clipping at a finite height. -/
def heatCappedOverlap (t : ℝ) (ht : 0 < t) (C : ℝ≥0) (x y : X) : ℝ :=
  ∫ z, min (hX.heatRadonDensity hn p t ht x z) C * min (hX.heatRadonDensity hn p t ht y z) C
    ∂hausdorff n X

omit [SeparableSpace X] [IsLocallyFiniteMeasure (hausdorff n X)] in
theorem heatCappedOverlap_integrable (t : ℝ) (ht : 0 < t) (C : ℝ≥0) (x y : X) :
    Integrable (fun z => min (hX.heatRadonDensity hn p t ht x z) C *
      min (hX.heatRadonDensity hn p t ht y z) C) (hausdorff n X) :=
  integrable_capped_product _ (hX.heatRadonDensity_integrable hn p t ht x)
    (hX.heatRadonDensity_integrable hn p t ht y)
    (hX.heatRadonDensity_nonneg hn p t ht x) (hX.heatRadonDensity_nonneg hn p t ht y) C

omit [SeparableSpace X] [IsLocallyFiniteMeasure (hausdorff n X)] in
theorem heatCappedOverlap_nonneg (t : ℝ) (ht : 0 < t) (C : ℝ≥0) (x y : X) :
    0 ≤ hX.heatCappedOverlap hn p t ht C x y :=
  integral_nonneg fun z => mul_nonneg
    (le_min (hX.heatRadonDensity_nonneg hn p t ht x z) C.coe_nonneg)
    (le_min (hX.heatRadonDensity_nonneg hn p t ht y z) C.coe_nonneg)

omit [SeparableSpace X] [IsLocallyFiniteMeasure (hausdorff n X)] in
theorem heatCappedOverlap_symmetric (t : ℝ) (ht : 0 < t) (C : ℝ≥0) (x y : X) :
    hX.heatCappedOverlap hn p t ht C x y = hX.heatCappedOverlap hn p t ht C y x := by
  simp only [heatCappedOverlap, mul_comm]

theorem heatCappedOverlap_le (t : ℝ) (ht : 0 < t) (C : ℝ≥0) (x y : X) :
    hX.heatCappedOverlap hn p t ht C x y ≤ C := by
  calc
    _ ≤ ∫ z, hX.heatRadonDensity hn p t ht x z * C ∂hausdorff n X := by
      apply integral_mono (hX.heatCappedOverlap_integrable hn p t ht C x y)
        ((hX.heatRadonDensity_integrable hn p t ht x).mul_const C)
      intro z
      exact mul_le_mul (min_le_left _ _) (min_le_right _ _)
        (le_min (hX.heatRadonDensity_nonneg hn p t ht y z) C.coe_nonneg)
        (hX.heatRadonDensity_nonneg hn p t ht x z)
    _ = C := by rw [integral_mul_const, hX.heatRadonDensity_mass_one hn p t ht x, one_mul]

theorem heatCappedOverlap_lipschitz (t : ℝ) (ht : 0 < t) (C : ℝ≥0) :
    LipschitzWith (2 * C * ⟨Real.sqrt (1 / (2*t*Real.exp (-2*|K| * t))), Real.sqrt_nonneg _⟩)
      (fun xy : X × X => hX.heatCappedOverlap hn p t ht C xy.1 xy.2) := by
  apply LipschitzWith.of_dist_le_mul
  intro xy zw
  change |hX.heatCappedOverlap hn p t ht C xy.1 xy.2 -
    hX.heatCappedOverlap hn p t ht C zw.1 zw.2| ≤
    (2 * (C : ℝ) * Real.sqrt (1 / (2*t*Real.exp (-2*|K| * t)))) * dist xy zw
  have h := integral_capped_product_sub_le (hausdorff n X)
    (hX.heatRadonDensity_integrable hn p t ht xy.1)
    (hX.heatRadonDensity_integrable hn p t ht xy.2)
    (hX.heatRadonDensity_integrable hn p t ht zw.1)
    (hX.heatRadonDensity_integrable hn p t ht zw.2)
    (hX.heatRadonDensity_nonneg hn p t ht xy.1)
    (hX.heatRadonDensity_nonneg hn p t ht xy.2)
    (hX.heatRadonDensity_nonneg hn p t ht zw.1)
    (hX.heatRadonDensity_nonneg hn p t ht zw.2) C
  refine h.trans ?_
  calc
    _ ≤ C * (Real.sqrt (1 / (2*t*Real.exp (-2*|K| * t))) * dist xy.1 zw.1 +
        Real.sqrt (1 / (2*t*Real.exp (-2*|K| * t))) * dist xy.2 zw.2) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (hX.heatRadonDensity_integral_abs_sub_le hn p t ht xy.1 zw.1)
        (hX.heatRadonDensity_integral_abs_sub_le hn p t ht xy.2 zw.2)) C.coe_nonneg
    _ ≤ C * (Real.sqrt (1 / (2*t*Real.exp (-2*|K| * t))) * dist xy zw +
        Real.sqrt (1 / (2*t*Real.exp (-2*|K| * t))) * dist xy zw) := by
      gcongr
      · exact le_max_left _ _
      · exact le_max_right _ _
    _ = _ := by ring

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
