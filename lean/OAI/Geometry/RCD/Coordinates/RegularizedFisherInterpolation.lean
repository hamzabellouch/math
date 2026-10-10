import OAI.Geometry.RCD.Heat.HeatFisherVariation

namespace OAI

/-! # The actual forward/backward regularized Fisher interpolation -/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

def regularizedFisherInterpolation (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
    (f w : Lp ℝ 2 μ) (ε T s : ℝ) : ℝ :=
  if hs : 0<T-s then ∫ x, heatAt μ hQ s w x *
    localGamma μ hQ (heatSobolev μ hQ (T-s) hs f) (heatSobolev μ hQ (T-s) hs f) x /
      (ε+heatAt μ hQ (T-s) f x) ∂μ else 0

namespace NoncollapsedRCD
variable {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) (hn : 2≤n) (p : X)
  [SeparableSpace X] [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn p

theorem regularizedFisherInterpolation_hasDerivAt
    (f w : Lp ℝ 2 (hausdorff n X)) (hf0 : 0≤f) (A B : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x|≤A) (hw : ∀ᵐ x ∂hausdorff n X, |w x|≤B)
    {T t ε : ℝ} (ht : 0<t) (htT : t<T) (hε : 0<ε) :
    let μ := hausdorff n X
    let Q := hX.quadratic
    let u := heatSobolev μ Q (T-t) (sub_pos.mpr htT) f
    let D := heatSobolevMap μ Q ((T-t)/2) (half_pos (sub_pos.mpr htT))
      (-heatGeneratorAt μ Q (T-t-(T-t)/2) f)
    HasDerivAt (regularizedFisherInterpolation μ Q f w ε T)
      ((∫ x, (-heatGeneratorAt μ Q t w) x*localGamma μ Q u u x /
        (ε+heatAt μ Q (T-t) f x) ∂μ)+
       (∫ x, heatAt μ Q t w x*SobolevSpace.toLp μ Q D x*localGamma μ Q u u x /
        (ε+heatAt μ Q (T-t) f x)^2 ∂μ)-
       2*(∫ x, heatAt μ Q t w x*localGamma μ Q u D x /
        (ε+heatAt μ Q (T-t) f x) ∂μ)) t := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let a := (T-t)/2
  have ha : 0<a := half_pos (sub_pos.mpr htT)
  have hat : a<T-t := by dsimp [a]; linarith
  have hd := hX.heat_fisher_tail_hasDerivAt hn p f w hf0 A B hf hw ha ht hat hε
  have hft := heatTail_eq μ Q a ha f (T-t) hat.le
  dsimp only at hd ⊢
  rw [hft,heatSobolev_toLp] at hd
  apply hd.congr_of_eventuallyEq
  have hnear : ∀ᶠ s in 𝓝 t, a<T-s := by
    exact (continuous_const.sub continuous_id).continuousAt.eventually (Ioi_mem_nhds hat)
  filter_upwards [hnear] with s hs
  have hpos : 0<T-s := ha.trans hs
  rw [regularizedFisherInterpolation,dite_eq_left hpos,heatTail_eq μ Q a ha f (T-s) hs.le,
    heatSobolev_toLp]

end NoncollapsedRCD
end RegularPointCoordinates

end

end OAI
