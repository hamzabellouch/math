import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Instances.Real.Lemmas

namespace OAI

/-! # Substitution of a convergent threshold in monotone functions -/
namespace JointDickman
open Filter
open scoped Topology

theorem moving_monotone_tendsto {ι : Type*} {L : Filter ι}
    {F : ι → ℝ → ℝ} {G : ℝ → ℝ} {v : ι → ℝ} {u : ℝ}
    (hF : ∀ x, Monotone (F x)) (hlim : ∀ t, Tendsto (fun x => F x t) L (𝓝 (G t)))
    (hG : ContinuousAt G u) (hv : Tendsto v L (𝓝 u)) :
    Tendsto (fun x => F x (v x)) L (𝓝 (G u)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hg : ∀ᶠ t in 𝓝[<] u, a < G t :=
      nhdsWithin_le_nhds (hG.tendsto.eventually (eventually_gt_nhds ha))
    obtain ⟨t,htg,htu⟩ := (hg.and self_mem_nhdsWithin).exists
    filter_upwards [(hlim t).eventually (eventually_gt_nhds htg),
      hv.eventually (eventually_gt_nhds htu)] with x hxa hxt
    exact hxa.trans_le (hF x hxt.le)
  · intro b hb
    have hg : ∀ᶠ t in 𝓝[>] u, G t < b :=
      nhdsWithin_le_nhds (hG.tendsto.eventually (eventually_lt_nhds hb))
    obtain ⟨t,htg,hut⟩ := (hg.and self_mem_nhdsWithin).exists
    filter_upwards [(hlim t).eventually (eventually_lt_nhds htg),
      hv.eventually (eventually_lt_nhds hut)] with x hxb hxt
    exact (hF x hxt.le).trans_lt hxb

end JointDickman

end OAI
