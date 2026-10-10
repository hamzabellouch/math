import OAI.Geometry.RCD.Heat.KernelHeatWindowBounds
import OAI.Geometry.RCD.Heat.DominatedProductPowerDerivative
import OAI.Geometry.RCD.Heat.KernelHeatProductDerivative

namespace OAI

/-! # Global power differentiation from an integrable heat-factor envelope -/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn p in
theorem kernelHeat_global_power_hasDerivAt (hK : K ≤ 0)
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (f g : Lp ℝ 2 (hausdorff n X)) (hf0 : 0 ≤ f) (hg0 : 0 ≤ g) (A B : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A)
    (hg : ∀ᵐ x ∂hausdorff n X, |g x| ≤ B)
    {a b T t : ℝ} (ha : 0 < a) (hb : b < T) (ht : t ∈ Ioo a b)
    (H : X → ℝ) (hH : Integrable H (hausdorff n X))
    (hEnv : ∀ r ∈ Ioo a b, ∀ x,
      kernelHeat (hausdorff n X) hX.quadratic hk r f x+
        kernelHeat (hausdorff n X) hX.quadratic hk (T-r) g x ≤ H x)
    (q : ℕ) (hi : Integrable (fun x =>
      (kernelHeat (hausdorff n X) hX.quadratic hk t f x*
        kernelHeat (hausdorff n X) hX.quadratic hk (T-t) g x)^q) (hausdorff n X)) :
    HasDerivAt (fun r => ∫ x,
      (kernelHeat (hausdorff n X) hX.quadratic hk r f x*
        kernelHeat (hausdorff n X) hX.quadratic hk (T-r) g x)^q ∂hausdorff n X)
      ((q:ℝ)*(∫ x,
        (kernelHeat (hausdorff n X) hX.quadratic hk t f x*
          kernelHeat (hausdorff n X) hX.quadratic hk (T-t) g x)^(q-1)*
          (kernelHeatGeneratorSource (hausdorff n X) hX.quadratic hk t f x*
              kernelHeat (hausdorff n X) hX.quadratic hk (T-t) g x-
            kernelHeat (hausdorff n X) hX.quadratic hk t f x*
              kernelHeatGeneratorSource (hausdorff n X) hX.quadratic hk (T-t) g x)
        ∂hausdorff n X)) t := by
  let m := hausdorff n X
  let Q := hX.quadratic
  let U := (n:ℝ)*(|K|+1/a)*A
  let V := (n:ℝ)*(|K|+1/(T-b))*B
  have htb : 0 < T-b := sub_pos.mpr hb
  have htt : 0 < T-t := sub_pos.mpr (ht.2.trans hb)
  have ht0 : 0 < t := ha.trans ht.1
  have hd := dominated_product_power_hasDerivAt (μ := m)
    (fun r x => kernelHeat m Q hk r f x) (fun r x => kernelHeat m Q hk (T-r) g x)
    (fun r x => kernelHeatGeneratorSource m Q hk r f x)
    (fun r x => -kernelHeatGeneratorSource m Q hk (T-r) g x)
    (Ioo_mem_nhds ht.1 ht.2)
    (fun r hr => (kernelHeat_continuous m Q hk (ha.trans hr.1) f).aestronglyMeasurable)
    (fun r hr => (kernelHeat_continuous m Q hk (sub_pos.mpr (hr.2.trans hb)) g).aestronglyMeasurable)
    (show AEStronglyMeasurable (kernelHeatGeneratorSource m Q hk t f) m from
      (kernelHeat_continuous m Q hk (half_pos ht0) _).aestronglyMeasurable)
    (show AEStronglyMeasurable (fun x => -kernelHeatGeneratorSource m Q hk (T-t) g x) m from
      (kernelHeat_continuous m Q hk (half_pos htt) _).neg.aestronglyMeasurable)
    q hi A.coe_nonneg B.coe_nonneg
    (show 0 ≤ U by dsimp only [U]; positivity)
    (show 0 ≤ V by dsimp only [V]; positivity) H hH (by
      apply Eventually.of_forall
      intro x r hr
      have hF := hX.kernelHeat_window_bounds hn p hK hk f hf0 A hf ha hr.1.le x
      have hG := hX.kernelHeat_window_bounds hn p hK hk g hg0 B hg htb
        (by linarith [hr.2] : T-b ≤ T-r) x
      refine ⟨hF.1,hG.1,hF.2,?_,hEnv r hr x,?_,?_⟩
      · simpa only [abs_neg] using hG.2
      · exact kernelHeat_generator_hasDerivAt m Q hk f (ha.trans hr.1) x
      · have hd := (kernelHeat_generator_hasDerivAt m Q hk g
          (sub_pos.mpr (hr.2.trans hb)) x).scomp r
          ((hasDerivAt_const r T).sub (hasDerivAt_id r))
        simpa only [Function.comp_def,zero_sub,neg_smul,one_smul] using hd)
  simpa only [mul_neg,← sub_eq_add_neg] using hd

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
