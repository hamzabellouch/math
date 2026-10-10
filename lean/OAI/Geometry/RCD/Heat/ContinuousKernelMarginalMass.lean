import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.ContinuousMap.Compact

namespace OAI

/-! # The two marginal masses of a continuous compact kernel

Fubini removes the scalar ambiguity of the logarithmic fixed point.
-/

open Set MeasureTheory
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

theorem continuous_kernel_marginal_mass (K : C(X × Y, ℝ)) (F : C(X, ℝ)) (G : C(Y, ℝ)) :
    (∫ x, F x*(∫ y, K (x,y)*G y ∂ν) ∂μ) =
      ∫ y, G y*(∫ x, K (x,y)*F x ∂μ) ∂ν := by
  let h := fun x y => F x*K (x,y)*G y
  have hc : Continuous (Function.uncurry h) :=
    ((F.continuous.comp continuous_fst).mul K.continuous).mul
      (G.continuous.comp continuous_snd)
  have hi : Integrable (Function.uncurry h) (μ.prod ν) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hswap := integral_integral_swap hi
  calc
    _ = ∫ x, ∫ y, h x y ∂ν ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change F x*(∫ y, K (x,y)*G y ∂ν) = ∫ y, h x y ∂ν
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by dsimp [h]; ring
    _ = ∫ y, ∫ x, h x y ∂μ ∂ν := hswap
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        change (∫ x, h x y ∂μ) = G y*(∫ x, K (x,y)*F x ∂μ)
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by dsimp [h]; ring

theorem continuous_kernel_constant_marginal (K : C(X × Y, ℝ)) (F : C(X, ℝ))
    (G : C(Y, ℝ)) {c : ℝ}
    (hrow : ∀ x, F x*(∫ y, K (x,y)*G y ∂ν)=c)
    (hcol : ∀ y, G y*(∫ x, K (x,y)*F x ∂μ)=1) : c=1 := by
  have h := continuous_kernel_marginal_mass μ ν K F G
  simpa [hrow,hcol] using h

end RegularPointCoordinates

end

end OAI
