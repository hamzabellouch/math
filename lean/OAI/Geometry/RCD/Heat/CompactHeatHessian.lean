import OAI.Geometry.RCD.Metric.CompactFactorL2
import OAI.Geometry.RCD.Heat.BoundedHeatSecondVariation

namespace OAI

/-! # Hessian second variation for the original compact heat factors

A single pair of initial L2 functions represents the original endpoint
factors for every positive time. Their pairing has the computed second
derivative on the whole open interpolation interval.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem compact_heat_bridge_hessian {S U : Set X}
    [CompactSpace S] [CompactSpace U]
    (μ : Measure S) (ν : Measure U) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    (F : C(S, ℝ)) (G : C(U, ℝ)) :
    ∃ (f g : Lp ℝ 2 (hausdorff n X)) (A B : ℝ≥0),
      (∀ᵐ x ∂hausdorff n X, |f x| ≤ A) ∧
      (∀ᵐ x ∂hausdorff n X, |g x| ≤ B) ∧
      (∀ (s : ℝ) (hs : 0 < s) (x : X),
        hX.compactHeatFactor hn p μ F s hs x =
          kernelHeat (hausdorff n X) hX.quadratic
            (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) s f x) ∧
      (∀ (s : ℝ) (hs : 0 < s) (x : X),
        hX.compactHeatFactor hn p ν G s hs x =
          kernelHeat (hausdorff n X) hX.quadratic
            (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) s g x) ∧
      ∀ (T t : ℝ) (ht : 0 < t) (htT : t < T)
        (h : Lp ℝ 2 (hausdorff n X)) (C : ℝ≥0),
        (∀ᵐ x ∂hausdorff n X, |h x| ≤ C) → ∀ (a : ℝ) (ha : 0 < a),
        let m := hausdorff n X
        let Q := hX.quadratic
        let u := heatSobolev m Q t ht f
        let v := heatSobolev m Q (T-t) (sub_pos.mpr htT) g
        let w := heatSobolev m Q a ha h
        ∃ (W : Lp ℝ ∞ m) (uv wu wv : SobolevSpace m Q),
          W =ᵐ[m] SobolevSpace.toLp m Q w ∧
          SobolevSpace.toLp m Q uv =ᵐ[m] localGamma m Q u v ∧
          SobolevSpace.toLp m Q wu =ᵐ[m] localGamma m Q w u ∧
          SobolevSpace.toLp m Q wv =ᵐ[m] localGamma m Q w v ∧
          HasDerivAt (deriv (fun s => ∫ x, W x*
            ((∫ y, hX.canonicalHeatKernel hn p s x y*F y ∂μ) *
              (∫ z, hX.canonicalHeatKernel hn p (T-s) x z*G z ∂ν)) ∂m))
            (inner ℝ (heatSecondGeneratorAt m Q a h)
                (SobolevSpace.toLp m Q (SobolevSpace.product m Q u v
                  A B))-
              4*(∫ x, localHessianAction m Q w u v wu wv uv x ∂m)) t := by
  obtain ⟨f,hf,he⟩ := hX.compact_heat_factor_L2 hn p μ ρ₀ hm₀ hp₀ hC₀ hμ F
  obtain ⟨g,hg,he'⟩ := hX.compact_heat_factor_L2 hn p ν ρ₁ hm₁ hp₁ hC₁ hν G
  obtain ⟨A,hA⟩ := hf
  obtain ⟨B,hB⟩ := hg
  refine ⟨f,g,A,B,hA,hB,he,he',?_⟩
  intro T t ht htT h C hh a ha
  obtain ⟨W,uv,wu,wv,hW,huv,hwu,hwv,hd⟩ :=
    hX.bounded_heat_second_variation hn p f g h A B C hA hB hh ht htT ha
  refine ⟨W,uv,wu,wv,hW,huv,hwu,hwv,?_⟩
  apply hd.congr_of_eventuallyEq
  apply Filter.EventuallyEq.deriv
  filter_upwards [Ioo_mem_nhds ht htT] with s hs
  apply integral_congr_ae
  exact Eventually.of_forall fun x => congrArg (fun z : ℝ => W x*z)
    (congrArg₂ (· * ·) (he s hs.1 x) (he' (T-s) (sub_pos.mpr hs.2) x))

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
