import OAI.Geometry.RCD.Heat.AlmostMonotoneTimeLimit
import OAI.Geometry.RCD.Sobolev.TimeEnvelopeLipschitz
import OAI.Geometry.RCD.Sobolev.DenseLipschitzUniformLimit

namespace OAI

/-! # Uniform spatial convergence outside countably many times

The exceptional set is chosen using one countable dense spatial family.
Consequently it works simultaneously at every spatial point.
-/

open Set Filter
open scoped NNReal Topology
noncomputable section
namespace RegularPointCoordinates

theorem almost_monotone_uniform_limit
    {Y : Type*} [MetricSpace Y] [CompactSpace Y] [Nonempty Y]
    {δ M : ℝ} (hM : 0 ≤ M) (s : ℕ → ℝ) (v : ℕ → Y → ℝ) (L : ℝ≥0)
    (hs : ∀ i, s i ∈ Icc δ 1)
    (hdense : ∀ a b : ℝ, δ ≤ a → b ≤ 1 → a < b → ∃ i, a < s i ∧ s i < b)
    (f : ℕ → ℝ → Y → ℝ) (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hb : ∀ k t, t ∈ Icc δ 1 → ∀ x, |f k t x| ≤ M)
    (hv : ∀ i x, |v i x| ≤ M)
    (hLv : ∀ i, LipschitzWith L (v i))
    (hLf : ∀ k t, t ∈ Icc δ 1 → LipschitzWith L (f k t))
    (hl : ∀ i x, Tendsto (fun k => f k (s i) x) atTop (𝓝 (v i x)))
    (ho : ∀ k a b, δ ≤ a → a ≤ b → b ≤ 1 → ∀ x,
      f k a x-f k b x ≤ e k*(b-a)) :
    ∃ N : Set ℝ, N.Countable ∧
      ∀ t ∈ Ioo δ 1, t ∉ N →
        TendstoUniformly (fun k => f k t)
          (fun x => timeLowerEnvelope M s (fun i => v i x) t) atTop := by
  let d := TopologicalSpace.denseSeq Y
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq Y
  let N := ⋃ i : ℕ, {t | ¬ContinuousAt (timeLowerEnvelope M s (fun j => v j (d i))) t}
  have hN : N.Countable := Set.countable_iUnion fun i =>
    timeLowerEnvelope_countable_discontinuities hM s (fun j => v j (d i)) (fun j => hv j (d i))
  refine ⟨N,hN,?_⟩
  intro t ht hnot
  apply dense_lipschitz_uniform_limit d hd (fun k => f k t) _ L
    (fun k => hLf k t ⟨ht.1.le,ht.2.le⟩)
    (timeLowerEnvelope_lipschitz hM s v L hv hLv t)
  intro i
  have hc : ContinuousAt (timeLowerEnvelope M s (fun j => v j (d i))) t := by
    by_contra hbad
    exact hnot (mem_iUnion.mpr ⟨i,hbad⟩)
  exact almost_monotone_time_limit hM s (fun j => v j (d i)) hs hdense
    (fun k u => f k u (d i)) e he (fun k u hu => hb k u hu (d i))
    (fun j => hv j (d i)) (fun j => hl j (d i))
    (fun k a b ha hab hb => ho k a b ha hab hb (d i)) ht hc

end RegularPointCoordinates

end

end OAI
