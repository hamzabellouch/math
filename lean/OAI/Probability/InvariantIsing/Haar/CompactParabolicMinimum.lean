import OAI.Probability.InvariantIsing.Magnetic.MagneticMinimumCalculus
import Mathlib.Topology.Order.Compact

namespace OAI

/-! The scalar minimum argument on a compact spatial state space. -/
noncomputable section
open Filter Set
open scoped Topology
namespace InvariantIsing

lemma compact_parabolic_nonneg {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]
    {T : ℝ} (hT : 0 ≤ T) (W : ℝ → K → ℝ) (Wt : ℝ × K → ℝ) (B : ℝ → K → ℝ)
    (hc : ContinuousOn (fun z : ℝ × K => W z.1 z.2) (Icc (0 : ℝ) T ×ˢ Set.univ))
    (hi : ∀ x, 0 ≤ W 0 x)
    (hd : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x, HasDerivAt (fun s => W s x) (Wt (t,x)) t)
    (hpde : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x, B t x-W t x ≤ Wt (t,x))
    (hspace : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, (∀ y, W t x ≤ W t y) → 0 ≤ B t x) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x, 0 ≤ W t x := by
  intro t ht x
  by_contra hn
  have hneg : W t x < 0 := lt_of_not_ge hn
  let x₀ : K := Classical.choice inferInstance
  obtain ⟨q,hq,hm⟩ := (isCompact_Icc.prod (isCompact_univ : IsCompact (Set.univ : Set K))).exists_isMinOn
    ⟨(0,x₀),⟨⟨le_rfl,hT⟩,Set.mem_univ x₀⟩⟩ hc
  have hqneg : W q.1 q.2 < 0 := (hm (show (t,x) ∈ Icc (0 : ℝ) T ×ˢ (Set.univ : Set K) from
      ⟨ht,Set.mem_univ x⟩)).trans_lt hneg
  have hqt : 0 < q.1 := by
    by_contra h
    have he : q.1=0 := le_antisymm (le_of_not_gt h) hq.1.1
    rw [he] at hqneg
    exact (not_lt_of_ge (hi q.2)) hqneg
  have hleft : ∀ᶠ s in 𝓝[<] q.1, W q.1 q.2 ≤ W s q.2 := by
    have hpos : ∀ᶠ s in 𝓝[<] q.1, 0 < s :=
      (show ∀ᶠ s : ℝ in 𝓝 q.1, 0 < s from Ioi_mem_nhds hqt).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [hpos,self_mem_nhdsWithin] with s hs hs'
    exact hm (show (s,q.2) ∈ Icc (0 : ℝ) T ×ˢ (Set.univ : Set K) from
      ⟨⟨hs.le,hs'.le.trans hq.1.2⟩,Set.mem_univ q.2⟩)
  have htime := derivative_nonpos_at_left_min (hd q.1 ⟨hqt,hq.1.2⟩ q.2) hleft
  have hsp := hspace q.1 hq.1 q.2 (fun y => hm (show (q.1,y) ∈ Icc (0 : ℝ) T ×ˢ (Set.univ : Set K) from
    ⟨hq.1,Set.mem_univ y⟩))
  have hp := hpde q.1 ⟨hqt,hq.1.2⟩ q.2
  linarith

end InvariantIsing

end

end OAI
