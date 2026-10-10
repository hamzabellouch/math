import OAI.Geometry.RCD.Heat.BoundedHeatOrder
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

namespace OAI

/-! # A Radon measure representing each bounded heat evaluation

The positive functional is the actual heat semigroup on compact continuous
data. Riesz--Markov constructs its representing measure, without assuming a
kernel or a density. Subsequent density arguments can therefore work with
the canonical measure rather than adding an existence premise.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal Topology CompactlySupported

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ]

/-- Compact continuous tests as actual L² classes. -/
def compactTestToL2 : C_c(X, ℝ) →ₗ[ℝ] Lp ℝ 2 μ where
  toFun f := (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport).toLp f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem compactTestToL2_coe (f : C_c(X, ℝ)) : compactTestToL2 μ f =ᵐ[μ] f :=
  (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport).coeFn_toLp

theorem compactTestToL2_mono {f g : C_c(X, ℝ)} (hfg : f ≤ g) :
    compactTestToL2 μ f ≤ compactTestToL2 μ g := by
  apply (Lp.coeFn_le _ _).mp
  filter_upwards [compactTestToL2_coe μ f, compactTestToL2_coe μ g] with x hx hy
  rw [hx, hy]
  exact hfg x

variable {n : ℕ}

theorem compactTestToL2_bounded [IsFiniteMeasureOnCompacts (hausdorff n X)] (f : C_c(X, ℝ)) :
    HasBoundedAmplitude (compactTestToL2 (hausdorff n X) f) := by
  refine ⟨‖f.toBoundedContinuousFunction‖₊, ?_⟩
  filter_upwards [compactTestToL2_coe (hausdorff n X) f] with x hx
  rw [hx]
  exact f.toBoundedContinuousFunction.norm_coe_le_norm x

namespace NoncollapsedRCD

variable {K : ℝ} (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (p : X)
  [ProperSpace X] [(hausdorff n X).Regular]

/-- Positive heat evaluation on compactly supported continuous functions. -/
def compactHeatEval (t : ℝ) (ht : 0 < t) (x : X) : C_c(X, ℝ) →ₚ[ℝ] ℝ where
  toFun f := hX.boundedHeat hn p (compactTestToL2 (hausdorff n X) f)
    (compactTestToL2_bounded f) t ht x
  map_add' f g := by
    exact congrFun (hX.boundedHeat_add hn p (compactTestToL2 (hausdorff n X) f)
      (compactTestToL2 (hausdorff n X) g) (compactTestToL2_bounded f)
      (compactTestToL2_bounded g) t ht) x
  map_smul' c f := by
    exact congrFun (hX.boundedHeat_smul hn p (compactTestToL2 (hausdorff n X) f)
      (compactTestToL2_bounded f) c t ht) x
  monotone' f g hfg := hX.boundedHeat_mono hn p _ _ _ _ t ht
    (compactTestToL2_mono (hausdorff n X) hfg) x

theorem compactHeatEval_abs_le (t : ℝ) (ht : 0 < t) (x : X)
    (f : C_c(X, ℝ)) (C : ℝ≥0) (hC : ∀ y, |f y| ≤ C) :
    |hX.compactHeatEval hn p t ht x f| ≤ C := by
  apply hX.boundedHeat_abs_le hn p _ _ t ht C
  filter_upwards [compactTestToL2_coe (hausdorff n X) f] with y hy
  rw [hy]
  exact hC y

/-- The canonical Radon heat measure at a fixed positive time and center. -/
def heatRadonMeasure (t : ℝ) (ht : 0 < t) (x : X) : Measure X :=
  RealRMK.rieszMeasure (hX.compactHeatEval hn p t ht x)

instance heatRadonMeasure_regular (t : ℝ) (ht : 0 < t) (x : X) :
    (hX.heatRadonMeasure hn p t ht x).Regular :=
  RealRMK.regular_rieszMeasure _

theorem heatRadonMeasure_integral (t : ℝ) (ht : 0 < t) (x : X)
    (f : C_c(X, ℝ)) :
    ∫ y, f y ∂hX.heatRadonMeasure hn p t ht x = hX.compactHeatEval hn p t ht x f :=
  RealRMK.integral_rieszMeasure _ f

end NoncollapsedRCD
end RegularPointCoordinates

end

end OAI
