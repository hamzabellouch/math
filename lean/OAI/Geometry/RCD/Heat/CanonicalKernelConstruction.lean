import OAI.Geometry.RCD.Heat.CanonicalL2Rows

namespace OAI

/-! # Construction of the continuous heat kernel

The actual heat semigroup supplies all the fields of the published
continuous-kernel premise without a Gaussian assumption.
The convolution identity holds at every pair of points by L² continuity
and full support, rather than only for almost every endpoint.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology InnerProductSpace

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem canonicalHeatKernel_product_integrable
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (x y : X) :
    Integrable (fun z => hX.canonicalHeatKernel hn p s x z *
      hX.canonicalHeatKernel hn p t z y) (hausdorff n X) := by
  have hi := L2.integrable_inner (𝕜 := ℝ)
    (hX.canonicalL2Row hn p s hs x) (hX.canonicalL2Row hn p t ht y)
  apply hi.congr
  filter_upwards [hX.canonicalL2Row_coe hn p s hs x,
    hX.canonicalL2Row_coe hn p t ht y] with z hx hy
  simp only [RCLike.inner_apply, conj_trivial, hx, hy]
  rw [hX.canonicalHeatKernel_symmetric hn p t y z, mul_comm]

theorem canonicalHeatKernel_convolution_eq_inner
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (x y : X) :
    (∫ z, hX.canonicalHeatKernel hn p s x z * hX.canonicalHeatKernel hn p t z y
      ∂hausdorff n X) =
      inner ℝ (hX.canonicalL2Row hn p s hs x) (hX.canonicalL2Row hn p t ht y) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hX.canonicalL2Row_coe hn p s hs x,
    hX.canonicalL2Row_coe hn p t ht y] with z hx hy
  simp only [RCLike.inner_apply, conj_trivial, hx, hy]
  rw [hX.canonicalHeatKernel_symmetric hn p t y z, mul_comm]

theorem canonicalHeatKernel_convolution_ae
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (x : X) :
    (fun y => ∫ z, hX.canonicalHeatKernel hn p s x z * hX.canonicalHeatKernel hn p t z y
      ∂hausdorff n X) =ᵐ[hausdorff n X] hX.canonicalHeatKernel hn p (s+t) x := by
  have hsym := Measure.ae_ae_of_ae_prod (hX.heatJointDensity_symmetric_ae hn p t ht)
  filter_upwards [hsym, hX.heatJointDensity_convolution_ae hn p s t hs ht x,
    hX.canonicalHeatKernel_ae hn p (s+t) (add_pos hs ht) x] with y hy hc hsum
  rw [hsum, ← hc.2]
  apply integral_congr_ae
  filter_upwards [hX.canonicalHeatKernel_ae hn p s hs x,
    hX.canonicalHeatKernel_ae hn p t ht y, hy] with z hx hz hsym
  rw [hX.canonicalHeatKernel_symmetric hn p t z y, hx, hz, hsym]

theorem canonicalHeatKernel_convolution
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (x y : X) :
    (∫ z, hX.canonicalHeatKernel hn p s x z * hX.canonicalHeatKernel hn p t z y
      ∂hausdorff n X) = hX.canonicalHeatKernel hn p (s+t) x y := by
  let := hX.openPos K n
  have hleft : Continuous (fun y => ∫ z, hX.canonicalHeatKernel hn p s x z *
      hX.canonicalHeatKernel hn p t z y ∂hausdorff n X) := by
    simpa only [hX.canonicalHeatKernel_convolution_eq_inner hn p s t hs ht] using!
      (continuous_const.inner (hX.canonicalL2Row_continuous hn p t ht) :
        Continuous (fun y => inner ℝ (hX.canonicalL2Row hn p s hs x)
          (hX.canonicalL2Row hn p t ht y)))
  have hright : Continuous (hX.canonicalHeatKernel hn p (s+t) x) :=
    hX.canonicalHeatKernel_continuous_right hn p (s+t) (add_pos hs ht) x
  exact congrFun (Measure.eq_of_ae_eq
    (hX.canonicalHeatKernel_convolution_ae hn p s t hs ht x) hleft hright) y

/-- The continuous-kernel premise follows from the actual semigroup,
local heat smoothing, and uniform L² tails. -/
theorem canonicalHeatKernel_isContinuousHeatKernel :
    IsContinuousHeatKernel (hausdorff n X) hX.quadratic (hX.canonicalHeatKernel hn p) where
  nonneg t _ := hX.canonicalHeatKernel_nonneg hn p t
  continuous_right := hX.canonicalHeatKernel_continuous_right hn p
  continuous_joint := hX.canonicalHeatKernel_continuous_joint hn p
  symmetric t _ := hX.canonicalHeatKernel_symmetric hn p t
  integrable := hX.canonicalHeatKernel_integrable hn p
  mass_one := hX.canonicalHeatKernel_mass_one hn p
  convolution_integrable := hX.canonicalHeatKernel_product_integrable hn p
  convolution := hX.canonicalHeatKernel_convolution hn p
  represents := hX.canonicalHeatKernel_represents hn p

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
