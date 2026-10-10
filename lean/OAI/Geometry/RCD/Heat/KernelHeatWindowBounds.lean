import OAI.Geometry.RCD.Heat.KernelHeatSourceUpper

namespace OAI

/-! # Uniform value and source bounds away from heat time zero -/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn p in
theorem kernelHeat_window_bounds (hK : K ≤ 0)
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (f : Lp ℝ 2 (hausdorff n X)) (hf0 : 0 ≤ f) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A)
    {a s : ℝ} (ha : 0 < a) (has : a ≤ s) (x : X) :
    kernelHeat (hausdorff n X) hX.quadratic hk s f x ∈ Icc (0:ℝ) A ∧
      |kernelHeatGeneratorSource (hausdorff n X) hX.quadratic hk s f x| ≤
        (n:ℝ)*(|K|+1/a)*A := by
  let m := hausdorff n X
  let Q := hX.quadratic
  have hs : 0 < s := ha.trans_le has
  have hp : 0 ≤ kernelHeat m Q hk s f x := by
    rw [kernelHeat_eq_integral m Q hk hs]
    apply integral_nonneg_of_ae
    filter_upwards [(Lp.coeFn_nonneg _).mpr hf0] with y hy
    exact mul_nonneg (hk.nonneg s hs x y) hy
  refine ⟨⟨hp,(le_abs_self _).trans ((hX.kernelHeat_bounded_regularity hn p hk f A hf s hs).2 x)⟩,?_⟩
  exact (hX.kernelHeat_source_abs_bound_nonneg hn p hK hk f hf0 A hf hs x).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl (one_div_le_one_div_of_le ha has))
        (Nat.cast_nonneg n)) A.coe_nonneg)

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
