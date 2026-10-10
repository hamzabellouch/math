import OAI.Geometry.RCD.Heat.BoundedHeatMixedGram
import OAI.Geometry.RCD.Heat.BoundedHeatSobolevData
import OAI.Geometry.RCD.Heat.HeatIteratedLaplacian
import OAI.Geometry.RCD.Heat.HeatBridgeSecondDerivative
import OAI.Geometry.RCD.Sobolev.SobolevSecondVariation

namespace OAI

/-! # The actual bounded heat bridge has the exact Hessian second variation

All spatial representatives, mixed Gram entries, and iterated sources are
constructed from the three original bounded L2 data. The spatial test is
a positive-time heat regularization. No second-order premise is assumed.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Topology InnerProductSpace
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  [(hausdorff n X).Regular] [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] (hn : 2 ≤ n) (p : X)

include hn p in
theorem bounded_heat_second_variation (f g h : Lp ℝ 2 (hausdorff n X))
    (A B C : ℝ≥0) (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A)
    (hg : ∀ᵐ x ∂hausdorff n X, |g x| ≤ B) (hh : ∀ᵐ x ∂hausdorff n X, |h x| ≤ C)
    {T t a : ℝ} (ht : 0 < t) (htT : t < T) (ha : 0 < a) :
    let μ := hausdorff n X
    let Q := hX.quadratic
    let u := heatSobolev μ Q t ht f
    let v := heatSobolev μ Q (T-t) (sub_pos.mpr htT) g
    let w := heatSobolev μ Q a ha h
    ∃ (W : Lp ℝ ∞ μ) (uv wu wv : SobolevSpace μ Q),
      W =ᵐ[μ] SobolevSpace.toLp μ Q w ∧
      SobolevSpace.toLp μ Q uv =ᵐ[μ] localGamma μ Q u v ∧
      SobolevSpace.toLp μ Q wu =ᵐ[μ] localGamma μ Q w u ∧
      SobolevSpace.toLp μ Q wv =ᵐ[μ] localGamma μ Q w v ∧
      HasDerivAt (deriv (fun s => ∫ x, W x*
        (kernelHeat μ Q (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) s f x*
          kernelHeat μ Q (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) (T-s) g x) ∂μ))
        (inner ℝ (heatSecondGeneratorAt μ Q a h)
            (SobolevSpace.toLp μ Q (SobolevSpace.product μ Q u v A B))-
          4*(∫ x, localHessianAction μ Q w u v wu wv uv x ∂μ)) t := by
  intro μ Q u v w
  obtain ⟨huB,Lu,huL⟩ := hX.bounded_heat_sobolev_data hn p f A hf ht
  obtain ⟨hvB,Lv,hvL⟩ := hX.bounded_heat_sobolev_data hn p g B hg (sub_pos.mpr htT)
  obtain ⟨hwB,-⟩ := hX.bounded_heat_sobolev_data hn p h C hh ha
  have hUm : MemLp (SobolevSpace.toLp μ Q u) ∞ μ :=
    memLp_top_of_bound (Lp.aestronglyMeasurable _) A (by simpa only [Real.norm_eq_abs] using huB)
  have hVm : MemLp (SobolevSpace.toLp μ Q v) ∞ μ :=
    memLp_top_of_bound (Lp.aestronglyMeasurable _) B (by simpa only [Real.norm_eq_abs] using hvB)
  have hWm : MemLp (SobolevSpace.toLp μ Q w) ∞ μ :=
    memLp_top_of_bound (Lp.aestronglyMeasurable _) C (by simpa only [Real.norm_eq_abs] using hwB)
  let U := hUm.toLp _
  let V := hVm.toLp _
  let W := hWm.toLp _
  obtain ⟨uv,huv⟩ := hX.bounded_heat_mixed_gram hn p f g A B hf hg ht (sub_pos.mpr htT)
  obtain ⟨wu,hwu⟩ := hX.bounded_heat_mixed_gram hn p h f C A hh hf ha ht
  obtain ⟨wv,hwv⟩ := hX.bounded_heat_mixed_gram hn p h g C B hh hg ha (sub_pos.mpr htT)
  obtain ⟨du,hduv,hdu⟩ := heat_generator_iterated_laplacian μ Q f ht
  obtain ⟨dv,hdvv,hdv⟩ := heat_generator_iterated_laplacian μ Q g (sub_pos.mpr htT)
  obtain ⟨dw,hdwv,hdw⟩ := heat_generator_iterated_laplacian μ Q h ha
  have hu : IsWeakLaplacian μ Q u (-heatGeneratorAt μ Q t f) := by
    simpa only [heatGeneratorAt_of_pos μ Q t ht] using heatSobolev_weak_laplacian μ Q t ht f
  have hv : IsWeakLaplacian μ Q v (-heatGeneratorAt μ Q (T-t) g) := by
    simpa only [heatGeneratorAt_of_pos μ Q (T-t) (sub_pos.mpr htT)] using
      heatSobolev_weak_laplacian μ Q (T-t) (sub_pos.mpr htT) g
  have hw : IsWeakLaplacian μ Q w (-heatGeneratorAt μ Q a h) := by
    simpa only [heatGeneratorAt_of_pos μ Q a ha] using heatSobolev_weak_laplacian μ Q a ha h
  have hid := sobolev_second_variation_hessian μ Q u v w du dv dw uv wu wv
    (-heatGeneratorAt μ Q t f) (-heatGeneratorAt μ Q (T-t) g) (-heatGeneratorAt μ Q a h)
    (heatSecondGeneratorAt μ Q t f) (heatSecondGeneratorAt μ Q (T-t) g)
    (heatSecondGeneratorAt μ Q a h) hu hv hw hdu hdv hdw hduv hdvv hdwv U V W
    hUm.coeFn_toLp hVm.coeFn_toLp hWm.coeFn_toLp huv hwu hwv A B C Lu Lv huB hvB hwB huL hvL
  have heq : heatBridgeSecondVariation μ Q W f g T t =
      inner ℝ (heatSecondGeneratorAt μ Q a h)
        (SobolevSpace.toLp μ Q (SobolevSpace.product μ Q u v A B))-
        4*(∫ x, localHessianAction μ Q w u v wu wv uv x ∂μ) := by
    rw [← hid]
    simp only [heatBridgeSecondVariation,u,v,heatSobolev_toLp,map_neg,
      inner_neg_left,inner_neg_right,neg_neg]
    ring
  refine ⟨W,uv,wu,wv,hWm.coeFn_toLp,huv,hwu,hwv,?_⟩
  rw [← heq]
  exact kernelHeat_bridge_pairing_second_hasDerivAt μ Q
    (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) W f g ht htT

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
