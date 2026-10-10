import OAI.Geometry.RCD.Coordinates.HeatRegularizedEntropy
import OAI.Geometry.RCD.Heat.BoundedHeatOrder

namespace OAI

/-! # Regularized entropy along actual RCD heat interpolation

The gradient bounds used in differentiating the nonlinear pairing are
provided by the proved bounded-data smoothing theorem.
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

theorem heat_entropy_interpolation_derivative {ε : ℝ} (hε : 0<ε)
    (f w : Lp ℝ 2 (hausdorff n X)) (hf0 : 0≤f) (A B : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x|≤A) (hw : ∀ᵐ x ∂hausdorff n X, |w x|≤B)
    {T t : ℝ} (ht : 0<t) (htT : t<T) :
    HasDerivAt (fun s => ∫ x, heatAt (hausdorff n X) hX.quadratic s w x *
      shiftedEntropy ε (heatAt (hausdorff n X) hX.quadratic (T-s) f x) ∂hausdorff n X)
      (∫ x, heatAt (hausdorff n X) hX.quadratic t w x *
        (localGamma (hausdorff n X) hX.quadratic
          (heatSobolev (hausdorff n X) hX.quadratic (T-t) (sub_pos.mpr htT) f)
          (heatSobolev (hausdorff n X) hX.quadratic (T-t) (sub_pos.mpr htT) f) x /
          (ε+heatAt (hausdorff n X) hX.quadratic (T-t) f x)) ∂hausdorff n X) t := by
  let L : ℝ≥0 := ⟨Real.sqrt ((A:ℝ)^2/(2*(T-t)*Real.exp (-2 * |K| * (T-t)))),Real.sqrt_nonneg _⟩
  apply heat_shiftedEntropy_hasDerivAt (hausdorff n X) hX.quadratic hε f w hf0 A B hf hw ht htT L
  apply SobolevSpace.minimalSlope_le_lipschitz (hausdorff n X) hX.quadratic
    (heatSobolev (hausdorff n X) hX.quadratic (T-t) (sub_pos.mpr htT) f)
    (hX.boundedHeat_lipschitz hn p f ⟨A,hf⟩ (T-t) (sub_pos.mpr htT) A hf)
  simpa only [heatSobolev_toLp] using hX.boundedHeat_represents hn p f ⟨A,hf⟩ (T-t) (sub_pos.mpr htT)

theorem heat_entropy_interpolation_monotone {ε : ℝ} (hε : 0<ε)
    (f w : Lp ℝ 2 (hausdorff n X)) (hf0 : 0≤f) (hw0 : 0≤w) (A B : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x|≤A) (hw : ∀ᵐ x ∂hausdorff n X, |w x|≤B)
    (T : ℝ) :
    MonotoneOn (fun s => ∫ x, heatAt (hausdorff n X) hX.quadratic s w x *
      shiftedEntropy ε (heatAt (hausdorff n X) hX.quadratic (T-s) f x) ∂hausdorff n X) (Icc 0 T) := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 T)
    (heat_shiftedEntropy_continuous μ Q hε f w hf0 A hf T).continuousOn
  · intro s hs
    rw [interior_Icc] at hs
    exact (hX.heat_entropy_interpolation_derivative hn p hε f w hf0 A B hf hw hs.1 hs.2).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [interior_Icc] at hs
    rw [(hX.heat_entropy_interpolation_derivative hn p hε f w hf0 A B hf hw hs.1 hs.2).deriv]
    apply integral_nonneg_of_ae
    filter_upwards [(Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ Q s w hw0),
      (Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ Q (T-s) f hf0),
      localGamma_self μ Q (heatSobolev μ Q (T-s) (sub_pos.mpr hs.2) f)] with x hw hf hΓ
    rw [hΓ]
    change 0 ≤ heatAt (hausdorff n X) hX.quadratic s w x at hw
    change 0 ≤ heatAt (hausdorff n X) hX.quadratic (T-s) f x at hf
    exact mul_nonneg hw (div_nonneg (sq_nonneg _) (add_nonneg hε.le hf))

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
