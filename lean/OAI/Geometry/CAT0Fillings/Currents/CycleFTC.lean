import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.BorelAction
import OAI.Geometry.CAT0Fillings.Currents.CycleDerivative
import OAI.Geometry.CAT0Fillings.Prism.TimeCoordinate
import OAI.Geometry.CAT0Fillings.Calculus.LipschitzFTC

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
local notation "BL" => boundedLipSubmodule (X := X)
lemma IsMetricCurrent.cycle_time_FTC {k : ℕ} {T : Functional X (k+1)}
    (hcur : IsMetricCurrent T) (hT : IntegerRectifiable T) (hz : IsCycle T)
    (μ : Measure X) [IsFiniteMeasure μ] (hμ : Controls T μ)
    (v : Fin (k+2) → ℝ × X → ℝ) (K : ℝ≥0) (hv : ∀ i, LipschitzWith K (v i))
    (a b : ℝ) :
    (∫ t in a..b, ∑ i, (-1:ℝ)^i.val * BorelCoefficients.borelAction μ hcur
      (fun x => deriv (fun s => v i (s,x)) t)
      (fun j x => v (i.succAbove j) (t,x))) =
      T (fun x => v 0 (b,x)) (fun j x => v j.succ (b,x)) -
      T (fun x => v 0 (a,x)) (fun j x => v j.succ (a,x)) := by
  let V (t : ℝ) (i : Fin (k+2)) : BL :=
    ⟨fun x => v i (t,x),boundedLip_of_lipschitz_compact (lipschitz_slice (hv i) t)⟩
  have hx (t i) : LipschitzWith K (V t i : X → ℝ) := lipschitz_slice (hv i) t
  have ht (i x) : LipschitzWith K (fun t => (V t i : X → ℝ) x) := lipschitz_time (hv i) x
  have hd : ∀ᵐ t ∂volume, HasDerivAt (fun s => hcur.fullMultilinear (V s))
      (∑ i, (-1:ℝ)^i.val * BorelCoefficients.borelAction μ hcur
        (fun x => deriv (fun s => v i (s,x)) t) (fun j x => v (i.succAbove j) (t,x))) t := by
    have ha : ∀ᵐ t ∂volume, ∀ i, ∀ᵐ x ∂μ, HasDerivAt (fun s => v i (s,x))
        (deriv (fun s => v i (s,x)) t) t :=
      ae_all_iff.mpr (fun i => ae_time_hasDeriv (hv i) μ)
    filter_upwards [ha] with t ha
    exact hcur.hasDeriv_cycle_path hT hz μ hμ V K hx ht t _
      (fun i => integrable_timeDeriv (hv i) μ t) ha
  have heq : (∫ t in a..b, ∑ i, (-1:ℝ)^i.val * BorelCoefficients.borelAction μ hcur
      (fun x => deriv (fun s => v i (s,x)) t)
      (fun j x => v (i.succAbove j) (t,x))) =
      ∫ t in a..b, deriv (fun s => hcur.fullMultilinear (V s)) t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hd] with t ht _
    exact ht.deriv.symm
  rw [heq,LipschitzWith.integral_deriv_eq_sub (hcur.cycle_time_lipschitz hT hz V K hx ht)]
  rfl

end CAT0Fillings

namespace CAT0Fillings
attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable
end CAT0Fillings

end
end

end OAI
