import OAI.Geometry.RCD.Heat.ActualHeatGrams

namespace OAI

/-! # Actual L² heat-kernel rows and their semigroup evolution -/

open Set Filter MeasureTheory
open scoped ENNReal NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ hQ ker)

include hk

/-- The kernel convolution identity itself gives square integrability. -/
theorem heatKernelRow_memLp (s : ℝ) (hs : 0 < s) (y : X) : MemLp (ker s y) 2 μ := by
  apply (memLp_two_iff_integrable_sq (hk.continuous_right s hs y).aestronglyMeasurable).mpr
  apply (hk.convolution_integrable s s hs hs y y).congr
  exact Eventually.of_forall fun z => by
    change ker s y z*ker s z y = (ker s y z)^2
    rw [hk.symmetric s hs z y,pow_two]

/-- A positive-time kernel row as an actual L² function. -/
def heatKernelRowLp (s : ℝ) (hs : 0 < s) (y : X) : Lp ℝ 2 μ :=
  (heatKernelRow_memLp μ hQ hk s hs y).toLp (ker s y)

theorem heatKernelRowLp_coe (s : ℝ) (hs : 0 < s) (y : X) :
    heatKernelRowLp μ hQ hk s hs y =ᵐ[μ] ker s y := MemLp.coeFn_toLp _

/-- The abstract L² heat evolution agrees with the next kernel row. -/
theorem heatAt_kernelRow (s T : ℝ) (hs : 0 < s) (hT : 0 < T) (y : X) :
    heatAt μ hQ T (heatKernelRowLp μ hQ hk s hs y) =ᵐ[μ]
      fun x => ker (T+s) x y := by
  let f := heatKernelRowLp μ hQ hk s hs y
  have hf : f =ᵐ[μ] ker s y := heatKernelRowLp_coe μ hQ hk s hs y
  have hi : Integrable f μ := (hk.integrable s hs y).congr hf.symm
  apply (hk.represents T hT f hi).symm.trans
  exact Eventually.of_forall fun x => by
    change (∫ z, ker T x z*f z ∂μ) = ker (T+s) x y
    rw [← hk.convolution T s hT hs x y]
    apply integral_congr_ae
    filter_upwards [hf] with z hz
    rw [hz,hk.symmetric s hs y z]

end RegularPointCoordinates

end

end OAI
