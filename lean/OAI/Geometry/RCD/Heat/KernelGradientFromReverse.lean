import OAI.Geometry.RCD.Heat.KernelRowL2
import OAI.Geometry.RCD.Heat.HeatReversePoincare

namespace OAI

/-! # A kernel-row gradient estimate from reverse Poincaré -/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A bound on the earlier kernel row controls the weak gradient of its
heat evolution. The remaining row retains its spatial Gaussian decay. -/
theorem NoncollapsedRCD.kernel_row_gradient_bound
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X) (p : X) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) :=
      locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    let μ := hausdorff n X
    letI : μ.Regular := inferInstance
    ∀ {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hX.quadratic ker)
      (s T : ℝ) (hs : 0 < s) (hT : 0 < T) (y : X) (M : ℝ≥0),
      (∀ z, ker s y z ≤ M) →
      ∀ᵐ x ∂μ, 2*T*Real.exp (-2*|K| *T)*
        (SobolevSpace.minimalSlope μ hX.quadratic
          (heatSobolev μ hX.quadratic T hT (heatKernelRowLp μ hX.quadratic hk s hs y)) x)^2 ≤
        M*ker (T+s) x y := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let : μ.Regular := inferInstance
  dsimp only
  intro ker hk s T hs hT y M hM
  let f := heatKernelRowLp μ hX.quadratic hk s hs y
  have hf : f =ᵐ[μ] ker s y := heatKernelRowLp_coe μ hX.quadratic hk s hs y
  have hfb : ∀ᵐ x ∂μ, |f x| ≤ M := by
    filter_upwards [hf] with x hx
    rw [hx,abs_of_nonneg (hk.nonneg s hs y x)]
    exact hM x
  let Q := boundedLpSquare μ f M M.coe_nonneg hfb
  have hQf : Q ≤ (M:ℝ) • f := by
    apply (Lp.coeFn_le _ _).mp
    filter_upwards [boundedLpSquare_coe μ f M M.coe_nonneg hfb,hf,Lp.coeFn_smul (M:ℝ) f] with x hq hx hm
    rw [hq,hm]
    change f x^2 ≤ (M:ℝ)*f x
    rw [hx]
    nlinarith [hk.nonneg s hs y x,hM x]
  have horder := heatAt_mono μ hX.quadratic T hQf
  rw [map_smul] at horder
  have hrev := hX.heat_reverse_poincare K n hn p f M hfb T hT
  filter_upwards [hrev,(Lp.coeFn_le _ _).mpr horder,
    Lp.coeFn_smul (M:ℝ) (heatAt μ hX.quadratic T f),
    heatAt_kernelRow μ hX.quadratic hk s T hs hT y] with x hr ho hm hkx
  rw [hm] at ho
  change heatAt μ hX.quadratic T Q x ≤ (M:ℝ)*heatAt μ hX.quadratic T f x at ho
  rw [hkx] at ho
  exact (le_trans (by nlinarith [sq_nonneg (heatAt μ hX.quadratic T f x)]) hr).trans ho

end RegularPointCoordinates

end

end OAI
