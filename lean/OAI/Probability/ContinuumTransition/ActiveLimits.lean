import OAI.Probability.ContinuumTransition.ConvolutionLimit

namespace OAI

section
open scoped Topology
open Set Filter Metric
noncomputable section
namespace ContinuumTemperature

lemma active_subseq_of_density_bound {Q : ℕ → Parameter → ℝ} {q : Parameter → ℝ}
    {P : ℕ → Parameter → ℝ} {p : Parameter → ℝ} {a : ℕ → ℝ} {a₀ : ℝ}
    (hQ : TendstoLocallyUniformlyOn Q q atTop pressureDomain)
    (hconv : ∀ n, ConvexOn ℝ pressureDomain (Q n)) (hq : ContinuousOn q pressureDomain)
    (ha : Tendsto a atTop (𝓝 a₀)) (hP : ∀ n, IsMeanField (Q n) (a n) (P n))
    (hp : IsMeanField q a₀ p) {X W : ℕ → Parameter} {x : Parameter}
    (hx : x ∈ pressureDomain) (hX : Tendsto X atTop (𝓝 x)) (hXS : ∀ n, X n ∈ pressureDomain)
    (hA : ∀ n, W n ∈ activeLifts (Q n) (a n) (P n) (X n))
    {D : ℝ} (hD : ∀ n, (W n).2 ∈ Icc 0 D) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w ∈ activeLifts q a₀ p x,
      Tendsto (W ∘ φ) atTop (𝓝 w) := by
  obtain ⟨d,_,φ,hφ,hd⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) D)).tendsto_subseq hD
  let V : ℕ → Parameter := fun n => unlift (a (φ n)) (W (φ n))
  let Y : ℕ → Parameter := fun n => shiftedField (a (φ n)) (X (φ n)) (W (φ n)).2
  let y := shiftedField a₀ x d
  have hy : y ∈ pressureDomain := hx
  have hXφ := hX.comp hφ.tendsto_atTop
  have haφ := ha.comp hφ.tendsto_atTop
  have hY : Tendsto Y atTop (𝓝 y) := by
    have hh := ((continuous_fst.tendsto x).comp hXφ).prodMk_nhds
      (((continuous_snd.tendsto x).comp hXφ).add
        ((((continuous_fst.tendsto x).comp hXφ).mul haφ).mul hd))
    simpa only [Y,y,shiftedField,Function.comp_def] using hh
  obtain ⟨C,hC⟩ := eventually_subgradients_bounded isOpen_pressureDomain
    (Eventually.of_forall fun n => hconv (φ n))
    (fun z hz => (hQ.tendsto_at hz).comp hφ.tendsto_atTop) hy hY
  have hVC : ∀ᶠ n in atTop, V n ∈ closedBall 0 C := by
    filter_upwards [hC] with n hn
    simpa only [mem_closedBall,dist_zero_right] using hn _ (hA (φ n)).2
  obtain ⟨v,_,ψ,hψ,hv⟩ := (isCompact_closedBall (0 : Parameter) C).tendsto_subseq' hVC.frequently
  let θ := φ ∘ ψ
  have hθ := (hφ.comp hψ).tendsto_atTop
  let w : Parameter := (v.1+a₀*v.2^2/2,v.2)
  have hV2 := (continuous_snd.tendsto v).comp hv
  have hW : Tendsto (W ∘ θ) atTop (𝓝 w) := by
    have hh := (((continuous_fst.tendsto v).comp hv).add
      (((ha.comp hθ).mul (hV2.pow 2)).div_const 2)).prodMk_nhds hV2
    simpa only [V,unlift,w,θ,Function.comp_def,sub_add_cancel,Prod.mk.eta] using hh
  have hxl := hX.comp hθ
  have hwl := (continuous_snd.tendsto w).comp hW
  have hpl := meanField_tendsto_of_bounded_maximizers (locallyUniform_reindex hQ hθ) hq
    (ha.comp hθ) (fun n => hP (θ n)) hp hx hxl (fun n => hXS (θ n))
    (fun n => ⟨(W (θ n)).2,hD (θ n),(hA (θ n)).1⟩)
  have hcost := quadraticCost_tendsto (locallyUniform_reindex hQ hθ) hq (ha.comp hθ) hwl hx hxl
  have hshift : Tendsto (fun n => shiftedField (a (θ n)) (X (θ n)) (W (θ n)).2) atTop
      (𝓝 (shiftedField a₀ x w.2)) :=
    ((continuous_fst.tendsto x).comp hxl).prodMk_nhds
      (((continuous_snd.tendsto x).comp hxl).add
        ((((continuous_fst.tendsto x).comp hxl).mul (ha.comp hθ)).mul hwl))
  have hunlift : Tendsto (fun n => unlift (a (θ n)) (W (θ n))) atTop (𝓝 (unlift a₀ w)) := by
    exact (((continuous_fst.tendsto w).comp hW).sub
      (((ha.comp hθ).mul (hwl.pow 2)).div_const 2)).prodMk_nhds hwl
  refine ⟨θ,hφ.comp hψ,w,⟨?_,?_⟩,hW⟩
  · exact tendsto_nhds_unique (hcost.congr (fun n => (hA (θ n)).1)) hpl
  · exact supportOn_varying_limit isOpen_pressureDomain (locallyUniform_reindex hQ hθ) hq
      (show shiftedField a₀ x w.2 ∈ pressureDomain from hx) hshift hunlift (Eventually.of_forall fun n => (hA (θ n)).2)

end ContinuumTemperature
end
end

end OAI
