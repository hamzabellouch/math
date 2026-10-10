import OAI.Geometry.RCD.Heat.HeatFisherCurvature
import OAI.Geometry.RCD.Coordinates.RegularizedFisherContinuity
import OAI.Geometry.RCD.Heat.FisherScalarComparison
import OAI.Geometry.RCD.Heat.HeatEntropyInterpolation

namespace OAI

/-! # The actual heat-flow reverse entropy inequality

This is the regularized entropy gap, with an explicit sufficient
short-time curvature factor, proved from logarithmic Bochner.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2≤n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn p

theorem heat_reverse_entropy
    (f w : Lp ℝ 2 (hausdorff n X)) (hf0 : 0≤f) (hw0 : 0≤w) (A B : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x|≤A) (hw : ∀ᵐ x ∂hausdorff n X, |w x|≤B)
    {T ε : ℝ} (hT : 0<T) (hε : 0<ε) :
    T*Real.exp (-2*|K| * T)*
      (∫ x, w x*localGamma (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic T hT f)
        (heatSobolev (hausdorff n X) hX.quadratic T hT f) x /
        (ε+heatAt (hausdorff n X) hX.quadratic T f x) ∂hausdorff n X) ≤
      (∫ x, heatAt (hausdorff n X) hX.quadratic T w x*shiftedEntropy ε (f x) ∂hausdorff n X)-
      (∫ x, w x*shiftedEntropy ε (heatAt (hausdorff n X) hX.quadratic T f x) ∂hausdorff n X) := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let I := regularizedFisherInterpolation μ Q f w ε T
  let F := fun s => ∫ x, heatAt μ Q s w x*shiftedEntropy ε (heatAt μ Q (T-s) f x) ∂μ
  have hI0 : 0≤I 0 := by
    dsimp only [I,regularizedFisherInterpolation]
    rw [dite_eq_left (by simpa using hT)]
    apply integral_nonneg_of_ae
    filter_upwards [(Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ Q 0 w hw0),
      (Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ Q (T-0) f hf0),
      localGamma_self μ Q (heatSobolev μ Q (T-0) (by simpa using hT) f)] with x hx hy hz
    rw [hz]
    exact div_nonneg (mul_nonneg hx (sq_nonneg _)) (add_nonneg hε.le hy)
  have hIc : ContinuousOn I (Ico 0 T) := by
    intro t ht
    exact (hX.regularizedFisherInterpolation_continuousAt hn p f w hf0 A hf ht.2 hε).continuousWithinAt
  have hId (t : ℝ) (ht : t∈Ioo 0 T) :=
    hX.regularizedFisherInterpolation_curvature hn p f w hf0 hw0 A B hf hw ht.1 ht.2 hε
  have hFc : ContinuousOn F (Icc 0 T) := (heat_shiftedEntropy_continuous μ Q hε f w hf0 A hf T).continuousOn
  have hFd (t : ℝ) (ht : t∈Ioo 0 T) : HasDerivAt F (I t) t := by
    have hd := hX.heat_entropy_interpolation_derivative hn p hε f w hf0 A B hf hw ht.1 ht.2
    simpa only [I,F,regularizedFisherInterpolation,dite_eq_left (sub_pos.mpr ht.2),mul_div_assoc] using hd
  have hh := fisher_entropy_lower hT hI0 hIc hId hFc hFd
  simpa only [I,F,regularizedFisherInterpolation,sub_zero,sub_self,heatAt_zero,one_apply_eq_self,
    dite_eq_left hT] using hh

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
