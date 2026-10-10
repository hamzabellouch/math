import OAI.Geometry.RCD.Heat.CompactHeatInterpolationMean
import OAI.Geometry.RCD.Heat.CompactHeatLaplacianRemainder
import OAI.Geometry.RCD.Heat.CompactHeatHessian
import OAI.Geometry.RCD.Heat.ScaledHeatBridgeSecondDerivative

namespace OAI

/-! # The scaled Hessian formula with its actual vanishing remainder

All directions represent the original compact heat factors. The test is
a fixed heat regularization, independent of the interpolation time.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal Topology InnerProductSpace
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
  {hn : 2 ≤ n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k}
  (D : hX.CompactHeatScalingData hn p μ ν ε hε)

theorem interpolationMean_hessian
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    (h : Lp ℝ 2 (hausdorff n X)) (C : ℝ≥0)
    (hh : ∀ᵐ x ∂hausdorff n X, |h x| ≤ C) {a : ℝ} (ha : 0 < a)
    (k : ℕ) (t : Ioo (0 : ℝ) 1) :
    let m := hausdorff n X
    let Q := hX.quadratic
    let w := heatSobolev m Q a ha h
    let H := kernelHeat m Q (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) a h
    ∃ (u v uv wu wv : SobolevSpace m Q),
      (SobolevSpace.toLp m Q u =ᵐ[m] fun x =>
        hX.compactHeatFactor hn p μ (D.left k) (ε k/4*t)
          (mul_pos (div_pos (hε k) (by norm_num)) t.property.1) x) ∧
      (SobolevSpace.toLp m Q v =ᵐ[m] fun x =>
        hX.compactHeatFactor hn p ν (D.right k) (ε k/4*(1-t))
          (mul_pos (div_pos (hε k) (by norm_num)) (sub_pos.mpr t.property.2)) x) ∧
      SobolevSpace.toLp m Q uv =ᵐ[m] localGamma m Q u v ∧
      SobolevSpace.toLp m Q wu =ᵐ[m] localGamma m Q w u ∧
      SobolevSpace.toLp m Q wv =ᵐ[m] localGamma m Q w v ∧
      HasDerivAt (deriv (D.interpolationMean H k))
        (D.laplacianRemainder h a k t -
          4*(ε k/4)^2*(∫ x, localHessianAction m Q w u v wu wv uv x ∂m)) t := by
  intro m Q w H
  let τ := ε k/4
  have hτ : 0 < τ := div_pos (hε k) (by norm_num)
  have ht : 0 < τ*(t:ℝ) := mul_pos hτ t.property.1
  have htτ : τ*(t:ℝ)<τ := by nlinarith [t.property.2]
  have hback : τ-τ*(t:ℝ)=ε k/4*(1-t) := by dsimp only [τ]; ring
  obtain ⟨f,hf,hef⟩ := hX.compact_heat_factor_L2 hn p μ ρ₀ hm₀ hp₀ hC₀ hμ (D.left k)
  obtain ⟨g,hg,heg⟩ := hX.compact_heat_factor_L2 hn p ν ρ₁ hm₁ hp₁ hC₁ hν (D.right k)
  obtain ⟨A,hA⟩ := hf
  obtain ⟨B,hB⟩ := hg
  let u := heatSobolev m Q (τ*t) ht f
  let v := heatSobolev m Q (τ-τ*t) (sub_pos.mpr htτ) g
  obtain ⟨W,uv,wu,wv,hW,huv,hwu,hwv,hd⟩ :=
    hX.bounded_heat_second_variation hn p f g h A B C hA hB hh ht htτ ha
  have hu : SobolevSpace.toLp m Q u =ᵐ[m] fun x =>
      hX.compactHeatFactor hn p μ (D.left k) (τ*t) ht x := by
    filter_upwards [kernelHeat_represents_L2 m Q
      (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) ht f] with x hx
    simpa only [u,heatSobolev_toLp] using hx.symm.trans (hef _ ht x).symm
  have hv : SobolevSpace.toLp m Q v =ᵐ[m] fun x =>
      hX.compactHeatFactor hn p ν (D.right k) (τ-τ*t) (sub_pos.mpr htτ) x := by
    filter_upwards [kernelHeat_represents_L2 m Q
      (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) (sub_pos.mpr htτ) g] with x hx
    simpa only [v,heatSobolev_toLp] using hx.symm.trans (heg _ (sub_pos.mpr htτ) x).symm
  have hi : inner ℝ (heatSecondGeneratorAt m Q a h)
      (SobolevSpace.toLp m Q (SobolevSpace.product m Q u v A B)) =
      ∫ x, heatSecondGeneratorAt m Q a h x*D.interpolationDensity k t x ∂m := by
    obtain ⟨huA,-⟩ := hX.bounded_heat_sobolev_data hn p f A hA ht
    obtain ⟨hvB,-⟩ := hX.bounded_heat_sobolev_data hn p g B hB (sub_pos.mpr htτ)
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [SobolevSpace.product_coe m Q u v A B huA hvB,hu,hv] with x hp hux hvx
    simp only [Real.inner_apply,hp,hux,hvx]
    change heatSecondGeneratorAt m Q a h x *
      ((∫ y, hX.canonicalHeatKernel hn p (τ*t) x y*D.left k y ∂μ)*
        (∫ z, hX.canonicalHeatKernel hn p (τ-τ*t) x z*D.right k z ∂ν)) =
      heatSecondGeneratorAt m Q a h x *
      ((∫ y, hX.canonicalHeatKernel hn p (ε k/4*t) x y*D.left k y ∂μ)*
        (∫ z, hX.canonicalHeatKernel hn p (ε k/4*(1-t)) x z*D.right k z ∂ν))
    rw [hback]
  have he := hd.unique (kernelHeat_bridge_pairing_second_hasDerivAt m Q
    (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) W f g ht htτ)
  have hs := kernelHeat_scaled_bridge_second_hasDerivAt m Q
    (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) W f g hτ t.property.1 t.property.2
  rw [← he,hi] at hs
  have hvalue : τ^2*((∫ x, heatSecondGeneratorAt m Q a h x*
        D.interpolationDensity k t x ∂m)-4*(∫ x, localHessianAction m Q w u v wu wv uv x ∂m)) =
      D.laplacianRemainder h a k t-
        4*(ε k/4)^2*(∫ x, localHessianAction m Q w u v wu wv uv x ∂m) := by
    dsimp only [laplacianRemainder,τ]
    ring
  rw [hvalue] at hs
  refine ⟨u,v,uv,wu,wv,hu,?_,huv,hwu,hwv,?_⟩
  · simpa only [hback] using hv
  · apply hs.congr_of_eventuallyEq
    apply Filter.EventuallyEq.deriv
    filter_upwards [Ioo_mem_nhds t.property.1 t.property.2] with s hs
    have hsf : 0 < τ*s := mul_pos hτ hs.1
    have hsg : 0 < τ-τ*s := by nlinarith [hs.2]
    have htimes : τ-τ*s=ε k/4*(1-s) := by dsimp only [τ]; ring
    apply integral_congr_ae
    filter_upwards [hW,kernelHeat_represents_L2 m Q
      (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) ha h] with x hWx hHx
    change H x * _ = W x * _
    rw [show H x=W x from hHx.trans hWx.symm,← hef _ hsf x,← heg _ hsg x]
    change W x *
      ((∫ y, hX.canonicalHeatKernel hn p (ε k/4*s) x y*D.left k y ∂μ)*
        (∫ z, hX.canonicalHeatKernel hn p (ε k/4*(1-s)) x z*D.right k z ∂ν)) =
      W x *((∫ y, hX.canonicalHeatKernel hn p (τ*s) x y*D.left k y ∂μ)*
        (∫ z, hX.canonicalHeatKernel hn p (τ-τ*s) x z*D.right k z ∂ν))
    rw [htimes]

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
