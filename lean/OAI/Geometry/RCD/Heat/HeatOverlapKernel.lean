import OAI.Geometry.RCD.Heat.HeatCappedOverlap
import OAI.Geometry.RCD.Heat.HeatDensityConvolution
import Mathlib.Topology.Semicontinuity.Basic

namespace OAI

/-! # A symmetric lower-semicontinuous version of the heat overlap -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

/-- Increasing continuous capped overlaps define an extended-real
kernel. Pointwise finiteness is kept separate from this construction. -/
def heatOverlapKernel (t : ℝ) (ht : 0 < t) (x y : X) : ℝ≥0∞ :=
  ⨆ i : ℕ, ENNReal.ofReal (hX.heatCappedOverlap hn p t ht i x y)

theorem heatOverlapKernel_lowerSemicontinuous (t : ℝ) (ht : 0 < t) :
    LowerSemicontinuous (fun xy : X × X => hX.heatOverlapKernel hn p t ht xy.1 xy.2) := by
  apply lowerSemicontinuous_iSup
  intro i
  exact (ENNReal.continuous_ofReal.comp (hX.heatCappedOverlap_lipschitz hn p t ht i).continuous).lowerSemicontinuous

omit [SeparableSpace X] [IsLocallyFiniteMeasure (hausdorff n X)] in
theorem heatOverlapKernel_symmetric (t : ℝ) (ht : 0 < t) (x y : X) :
    hX.heatOverlapKernel hn p t ht x y = hX.heatOverlapKernel hn p t ht y x := by
  simp only [heatOverlapKernel, hX.heatCappedOverlap_symmetric hn p t ht]

omit [SeparableSpace X] [IsLocallyFiniteMeasure (hausdorff n X)] in
theorem heatOverlapKernel_eq_lintegral (t : ℝ) (ht : 0 < t) (x y : X) :
    hX.heatOverlapKernel hn p t ht x y =
      ∫⁻ z, ENNReal.ofReal (hX.heatRadonDensity hn p t ht x z) *
        ENNReal.ofReal (hX.heatRadonDensity hn p t ht y z) ∂hausdorff n X := by
  let a := hX.heatRadonDensity hn p t ht x
  let b := hX.heatRadonDensity hn p t ht y
  let f (i : ℕ) (z : X) := ENNReal.ofReal (min (a z) (i : ℝ) * min (b z) (i : ℝ))
  have hm (i : ℕ) : Measurable (f i) :=
    (((hX.heatRadonDensity_measurable hn p t ht x).min measurable_const).mul
      ((hX.heatRadonDensity_measurable hn p t ht y).min measurable_const)).ennreal_ofReal
  have hmono : Monotone f := by
    intro i j hij z
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul (min_le_min_left _ (by exact_mod_cast hij))
      (min_le_min_left _ (by exact_mod_cast hij))
      (le_min (hX.heatRadonDensity_nonneg hn p t ht y z) (by positivity))
      (le_min (hX.heatRadonDensity_nonneg hn p t ht x z) (by positivity))
  have hi (i : ℕ) : ENNReal.ofReal (hX.heatCappedOverlap hn p t ht i x y) =
      ∫⁻ z, f i z ∂hausdorff n X :=
    ofReal_integral_eq_lintegral_ofReal (hX.heatCappedOverlap_integrable hn p t ht i x y)
      (Eventually.of_forall fun z => mul_nonneg
        (le_min (hX.heatRadonDensity_nonneg hn p t ht x z) (by positivity))
        (le_min (hX.heatRadonDensity_nonneg hn p t ht y z) (by positivity)))
  rw [heatOverlapKernel]
  simp_rw [hi]
  rw [← lintegral_iSup hm hmono]
  apply lintegral_congr
  intro z
  apply le_antisymm
  · apply iSup_le
    intro i
    rw [← ENNReal.ofReal_mul (hX.heatRadonDensity_nonneg hn p t ht x z)]
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul (min_le_left _ _) (min_le_left _ _)
      (le_min (hX.heatRadonDensity_nonneg hn p t ht y z) (by positivity))
      (hX.heatRadonDensity_nonneg hn p t ht x z)
  · obtain ⟨i, hi⟩ := exists_nat_ge (max (a z) (b z))
    apply le_iSup_of_le i
    have ha : a z ≤ i := (le_max_left _ _).trans hi
    have hb : b z ≤ i := (le_max_right _ _).trans hi
    dsimp only [f]
    rw [min_eq_left ha, min_eq_left hb,
      ENNReal.ofReal_mul (hX.heatRadonDensity_nonneg hn p t ht x z)]

/-- At each starting point the symmetric overlap is the actual heat
density at double time, up to a null set of endpoints. -/
theorem heatOverlapKernel_ae (t : ℝ) (ht : 0 < t) (x : X) :
    hX.heatOverlapKernel hn p t ht x =ᵐ[hausdorff n X]
      fun y => ENNReal.ofReal (hX.heatJointDensity hn p (t+t) (add_pos ht ht) x y) := by
  have hs := Measure.ae_ae_of_ae_prod (hX.heatJointDensity_symmetric_ae hn p t ht)
  filter_upwards [hs, hX.heatDensityConvolution_ae hn p t t ht ht x] with y hy hc
  rw [hX.heatOverlapKernel_eq_lintegral hn p t ht x y]
  calc
    _ = ∫⁻ z, ENNReal.ofReal (hX.heatJointDensity hn p t ht x z) *
        ENNReal.ofReal (hX.heatJointDensity hn p t ht z y) ∂hausdorff n X := by
      apply lintegral_congr_ae
      filter_upwards [hX.heatJointDensity_ae hn p t ht x, hX.heatJointDensity_ae hn p t ht y, hy]
        with z hx hz hs
      rw [← hx, ← hz]
      exact congrArg (fun a => ENNReal.ofReal (hX.heatJointDensity hn p t ht x z) * ENNReal.ofReal a) hs
    _ = _ := hc

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
