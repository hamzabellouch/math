import OAI.Geometry.RCD.Heat.KernelGradientFromReverse
import OAI.Geometry.RCD.Heat.KernelHalfBound
import OAI.Geometry.RCD.Heat.GaussianGradientAlgebra
import OAI.Geometry.RCD.Heat.HeatHalfVolume
import OAI.Geometry.RCD.Sobolev.LocalGradientLipschitz
import OAI.Geometry.RCD.Heat.HeatKernelDifferenceInput

namespace OAI

/-! # The localized Gaussian heat difference estimate from the actual RCD flow -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal NNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The finite-difference estimate uses only a coarse Gaussian upper bound,
the proved reverse Poincaré inequality, and actual CD volume comparison. -/
theorem NoncollapsedRCD.gaussianHeatDifferenceBounds_of_upper {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [ProperSpace X] [(hausdorff n X).Regular]
    (hn : 2 ≤ n) {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    {C B : ℝ} (hC : 0 < C) (hB : 0 ≤ B)
    (hupper : ∀ t, 0 < t → ∀ x y,
      ker t x y ≤ C/(hausdorff n X).real (ball y (Real.sqrt t))*
        Real.exp (-dist x y^2/(5*t)+B*t)) :
    HasGaussianHeatDifferenceBounds (hausdorff n X) ker := by
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  obtain ⟨D,hD,hvol⟩ := hX.heat_half_volume_comparison hn
  let A := C*D*Real.exp 1
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨2*A,20,B+|K|,by positivity,by norm_num,add_nonneg hB (abs_nonneg K),?_⟩
  intro t ht ht1 x y z hxy
  let r := Real.sqrt t
  let V := μ.real (ball z r)
  have hr : 0 < r := Real.sqrt_pos.mpr ht
  have hr2 : r^2 = t := Real.sq_sqrt ht.le
  have hV : 0 < V := ENNReal.toReal_pos (hX.fullSupport z r hr).ne'
    (hX.finiteOnBounded _ isBounded_ball).ne
  have hVh : 0 < μ.real (ball z (Real.sqrt (t/2))) :=
    ENNReal.toReal_pos (hX.fullSupport z _ (Real.sqrt_pos.mpr (half_pos ht))).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne
  let Mp : ℝ≥0 := ⟨C*D/V*Real.exp (B*t),by positivity⟩
  have hMp : ∀ w, ker (t/2) z w ≤ Mp :=
    kernel_half_uniform_bound μ hX.quadratic hk hC hB hupper ht z hV hVh (hvol t ht ht1 z)
  let f := heatKernelRowLp μ hX.quadratic hk (t/2) (half_pos ht) z
  let u := heatSobolev μ hX.quadratic (t/2) (half_pos ht) f
  have hurep : SobolevSpace.toLp μ hX.quadratic u =ᵐ[μ] fun w => ker t w z := by
    simpa only [u,f,heatSobolev_toLp,show t/2+t/2=t by ring] using
      heatAt_kernelRow μ hX.quadratic hk (t/2) (t/2) (half_pos ht) (half_pos ht) z
  have hraw : ∀ᵐ w ∂μ, (t*Real.exp (-|K| *t))*
      (SobolevSpace.minimalSlope μ hX.quadratic u w)^2 ≤ Mp*ker t w z := by
    simpa only [u,f,show 2*(t/2)=t by ring,show -2*|K| *(t/2) = -|K| *t by ring,
      show t/2+t/2=t by ring] using
      hX.kernel_row_gradient_bound K n hn x hk (t/2) (t/2) (half_pos ht) (half_pos ht) z Mp hMp
  let E := Real.exp (-dist x z^2/(20*t)+(B+|K|)*t)
  let L : ℝ≥0 := ⟨A/(r*V)*E,by dsimp [E]; positivity⟩
  let M : ℝ≥0 := ⟨A/V*E,by dsimp [E]; positivity⟩
  have hlocal (w : X) (hw : dist x w ≤ 2*r) :
      ker t w z ≤ C*Real.exp 1/V*Real.exp (-dist x z^2/(10*t)+B*t) :=
    (hupper t ht w z).trans (gaussian_upper_local ht hC.le hV x z w hw)
  have hMv : ∀ w, dist x w ≤ 2*r → |ker t w z| ≤ M := by
    intro w hw
    rw [abs_of_nonneg (hk.nonneg t ht w z)]
    exact (hlocal w hw).trans (gaussian_amplitude_algebra hC hD hV ht (abs_nonneg K))
  have hLg : ∀ᵐ w ∂μ, dist x w ≤ 2*r → SobolevSpace.minimalSlope μ hX.quadratic u w ≤ L := by
    filter_upwards [hraw] with w hw
    intro hdist
    have hest := hw.trans (mul_le_mul_of_nonneg_left (hlocal w hdist) Mp.coe_nonneg)
    exact gaussian_gradient_algebra hC hD hV ht hr hr2 (abs_nonneg K) hest
  have hv : Continuous (fun w => ker t w z) :=
    (hk.continuous_right t ht z).congr (fun w => hk.symmetric t ht z w)
  have hd := hX.local_lipschitz_of_gradient K n hn u (fun w => ker t w z) hv hurep
    x r hr L M hMv hLg y hxy
  change |ker t x z-ker t y z| ≤
    Real.sqrt (2*(A/(r*V)*E)^2+2*(A/V*E)^2*(r⁻¹)^2)*dist x y at hd
  rw [gaussian_cutoff_factor hA.le (Real.exp_pos _).le hr hV] at hd
  exact hd.trans_eq (by dsimp only [r,V,E]; ring)

/-- Compatibility with the published two-sided input. -/
theorem NoncollapsedRCD.gaussianHeatDifferenceBounds {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [ProperSpace X] [(hausdorff n X).Regular]
    (hn : 2 ≤ n) {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (hg : HasGaussianHeatBounds (hausdorff n X) ker) :
    HasGaussianHeatDifferenceBounds (hausdorff n X) ker := by
  obtain ⟨C,B,hC,hB,hupper⟩ := hg.upper_five (hausdorff n X)
  exact hX.gaussianHeatDifferenceBounds_of_upper hn hk hC hB hupper

end RegularPointCoordinates

end

end OAI
