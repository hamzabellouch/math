import OAI.Geometry.RCD.Coordinates.ScalingNormalizationLimit

namespace OAI

/-! # Dual potentials from exact compact scaling normalization

The support of the second marginal is retained explicitly. Each row has
zero maximal limiting slack on that support.
-/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace Y]
  [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
  (ν : Measure Y) [IsProbabilityMeasure ν]

theorem scaling_dual_potential (K : ℕ → C(X × Y, ℝ))
    (F : ℕ → C(X, ℝ)) (G : ℕ → C(Y, ℝ)) (ε : ℕ → ℝ) (x₀ : X) (y₀ : Y)
    (hε : ∀ k, 0 < ε k) (hε0 : Tendsto ε atTop (𝓝 0))
    (hK : ∀ k z, 0 < K k z) (hF : ∀ k x, 0 < F k x) (hG : ∀ k y, 0 < G k y)
    (hrow : ∀ k x, F k x*(∫ y, K k (x,y)*G k y ∂ν)=1)
    (q : X × Y → ℝ) (f : X → ℝ) (g : Y → ℝ)
    (hq : Continuous q) (hg : Continuous g)
    (hkernel : TendstoUniformly (fun k z => ε k*Real.log (K k z)) q atTop)
    (hleft : TendstoUniformly (fun k x => ε k*(Real.log (F k x)-Real.log (F k x₀))) f atTop)
    (hright : TendstoUniformly (fun k y => ε k*(Real.log (G k y)-Real.log (G k y₀))) g atTop) :
    ∃ c : ℝ,
      Tendsto (fun k => ε k*(Real.log (F k x₀)+Real.log (G k y₀))) atTop (𝓝 c) ∧
      (∀ x y, y ∈ ν.support → f x+q (x,y)+g y+c ≤ 0) ∧
      ∀ x, ∃ y ∈ ν.support, f x+q (x,y)+g y+c=0 := by
  let row := fun x k => (⟨fun y => K k (x,y),
    (K k).continuous.comp (continuous_const.prodMk continuous_id)⟩ : C(Y,ℝ))
  have hlim (x : X) := scaling_normalization_limit ν (row x) G (fun k => F k x) ε y₀
    (fun k => hF k x) hε hε0 (fun k y => hK k (x,y)) hG (fun k => hrow k x)
    (fun y => q (x,y)) g (hq.comp (continuous_const.prodMk continuous_id)) hg
    (hkernel.comp (fun y => (x,y))) hright
  obtain ⟨y,hy,_,hc⟩ := hlim x₀
  let c := -(q (x₀,y)+g y)
  refine ⟨c,hc,?_,?_⟩
  · intro x z hz
    obtain ⟨w,hw,hm,hl⟩ := hlim x
    have he : f x+c = -(q (x,w)+g w) := by
      apply tendsto_nhds_unique _ hl
      apply ((hleft.tendsto_at x).add hc).congr'
      exact Eventually.of_forall fun k => by ring
    have hh := hm z hz
    linarith
  · intro x
    obtain ⟨w,hw,_,hl⟩ := hlim x
    have he : f x+c = -(q (x,w)+g w) := by
      apply tendsto_nhds_unique _ hl
      apply ((hleft.tendsto_at x).add hc).congr'
      exact Eventually.of_forall fun k => by ring
    exact ⟨w,hw,by linarith⟩

end RegularPointCoordinates

end

end OAI
