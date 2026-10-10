import OAI.Geometry.RCD.Heat.CanonicalHeatKernel
import OAI.Geometry.RCD.Heat.HeatKernelRows
import OAI.Geometry.RCD.Heat.GaussianHeatInput

namespace OAI

/-! # Identification with every published continuous heat-kernel representative

The canonical half-time overlap agrees pointwise with any continuous
kernel representing the actual Cheeger semigroup. Thus published Gaussian
estimates for such a kernel transfer to the canonical representative.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {ker : ℝ → X → X → ℝ}

theorem heatRadonDensity_ae_kernel
    (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (t : ℝ) (ht : 0 < t) (x : X) :
    hX.heatRadonDensity hn p t ht x =ᵐ[hausdorff n X] ker t x := by
  let μ := hausdorff n X
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    (hX.heatRadonDensity_integrable hn p t ht x) (hk.integrable t ht x)
  intro S hS hfin
  let f := indicatorConstLp 2 hS hfin.ne (1 : ℝ)
  have hfb := indicatorConstLp_abs_le_one μ hS hfin.ne
  have hfi : Integrable f μ :=
    ((integrableOn_const (C := (1 : ℝ)) hfin.ne).integrable_indicator hS).congr
      (indicatorConstLp_coeFn (p := 2) (hs := hS) (hμs := hfin.ne) (c := (1 : ℝ))).symm
  have heq : hX.boundedHeat hn p f ⟨1, hfb⟩ t ht = kernelHeat μ hX.quadratic hk t f :=
    hX.boundedHeat_unique hn p f ⟨1, hfb⟩ t ht
      (kernelHeat_continuous μ hX.quadratic hk ht f)
      (kernelHeat_represents μ hX.quadratic hk ht f hfi).symm
  calc
    _ = (hX.heatRadonMeasure hn p t ht x).real S :=
      Measure.setIntegral_toReal_rnDeriv (hX.heatRadonMeasure_absolutelyContinuous hn p t ht x) S
    _ = ∫ y, f y ∂hX.heatRadonMeasure hn p t ht x :=
      (hX.heatRadonMeasure_integral_indicator hn p t ht x hS hfin.ne).symm
    _ = hX.boundedHeat hn p f ⟨1, hfb⟩ t ht x :=
      hX.heatRadonMeasure_integral_bounded hn p t ht x f 1 hfb
    _ = kernelHeat μ hX.quadratic hk t f x := congrFun heq x
    _ = ∫ y, ker t x y * f y ∂μ := kernelHeat_eq_integral μ hX.quadratic hk ht f x
    _ = ∫ y in S, ker t x y ∂μ := by
      rw [← integral_indicator hS]
      apply integral_congr_ae
      filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hS) (hμs := hfin.ne)
        (c := (1 : ℝ))] with y hy
      change ker t x y * f y = S.indicator (fun y => ker t x y) y
      change f y = S.indicator (fun _ => (1 : ℝ)) y at hy
      rw [hy]
      by_cases hs : y ∈ S <;> simp [hs]

theorem canonicalHeatKernel_eq_of_isContinuousHeatKernel
    (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (t : ℝ) (ht : 0 < t) (x y : X) : hX.canonicalHeatKernel hn p t x y = ker t x y := by
  rw [canonicalHeatKernel, dite_eq_left ht, hX.heatOverlapKernel_eq_lintegral hn p]
  have he : (∫⁻ z, ENNReal.ofReal (hX.heatRadonDensity hn p (t/2) (half_pos ht) x z) *
      ENNReal.ofReal (hX.heatRadonDensity hn p (t/2) (half_pos ht) y z) ∂hausdorff n X) =
      ENNReal.ofReal (ker t x y) := by
    calc
      _ = ∫⁻ z, ENNReal.ofReal (ker (t/2) x z * ker (t/2) z y) ∂hausdorff n X := by
        apply lintegral_congr_ae
        filter_upwards [hX.heatRadonDensity_ae_kernel hn p hk (t/2) (half_pos ht) x,
          hX.heatRadonDensity_ae_kernel hn p hk (t/2) (half_pos ht) y] with z hx hy
        rw [hx, hy, hk.symmetric (t/2) (half_pos ht) y z,
          ENNReal.ofReal_mul (hk.nonneg (t/2) (half_pos ht) x z)]
      _ = ENNReal.ofReal (∫ z, ker (t/2) x z * ker (t/2) z y ∂hausdorff n X) :=
        (ofReal_integral_eq_lintegral_ofReal
          (hk.convolution_integrable (t/2) (t/2) (half_pos ht) (half_pos ht) x y)
          (Eventually.of_forall fun z => mul_nonneg (hk.nonneg _ (half_pos ht) x z)
            (hk.nonneg _ (half_pos ht) z y))).symm
      _ = _ := by rw [hk.convolution _ _ (half_pos ht) (half_pos ht), add_halves]
  rw [he, ENNReal.toReal_ofReal (hk.nonneg t ht x y)]

theorem canonicalHeatKernel_gaussian_of_published_kernel
    (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (hg : HasGaussianHeatBounds (hausdorff n X) ker) :
    HasGaussianHeatBounds (hausdorff n X) (hX.canonicalHeatKernel hn p) := by
  intro ε hε hε1
  obtain ⟨C₁, C₂, hC₁, hC₂, hG⟩ := hg ε hε hε1
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro t ht x y
  rw [hX.canonicalHeatKernel_eq_of_isContinuousHeatKernel hn p hk t ht x y]
  exact hG t ht x y

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
