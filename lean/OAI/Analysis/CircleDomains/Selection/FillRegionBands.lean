import OAI.Analysis.CircleDomains.Selection.FillRegionPotential

namespace OAI

/-! Filling an open region by one cannot enlarge a boundary band at any
point away from the region's frontier. This assertion is pointwise. -/

open Set Filter
open scoped Topology ENNReal

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem fillRegionOne_band
    (G V : Set X) (hV : IsOpen V) (u : X → ℝ) {s : X}
    (hs : s ∈ closure G) (hsfront : s ∉ frontier V) (a : ℝ≥0∞)
    (hband : ENNReal.ofReal (limsup u (𝓝[G] s) - liminf u (𝓝[G] s)) ≤ a) :
    ENNReal.ofReal (limsup (fillRegionOne V u) (𝓝[G] s) -
      liminf (fillRegionOne V u) (𝓝[G] s)) ≤ a := by
  let : NeBot (𝓝[G] s) := mem_closure_iff_nhdsWithin_neBot.mp hs
  by_cases hsV : s ∈ V
  · have hev : ∀ᶠx in 𝓝[G] s, x ∈ V := nhdsWithin_le_nhds (hV.mem_nhds hsV)
    have heq : fillRegionOne V u =ᶠ[𝓝[G] s] fun _ => (1 : ℝ) := by
      filter_upwards [hev] with x hx
      exact ite_eq_left hx
    rw [limsup_congr heq, liminf_congr heq, limsup_const, liminf_const,
      sub_self, ENNReal.ofReal_zero]
    exact bot_le
  · have hscl : s ∉ closure V := by
      intro h
      apply hsfront
      rw [hV.frontier_eq]
      exact ⟨h, hsV⟩
    have hev : ∀ᶠx in 𝓝[G] s, x ∉ closure V :=
      nhdsWithin_le_nhds (isClosed_closure.isOpen_compl.mem_nhds hscl)
    have heq : fillRegionOne V u =ᶠ[𝓝[G] s] u := by
      filter_upwards [hev] with x hx
      exact ite_eq_right (fun h => hx (subset_closure h))
    rwa [limsup_congr heq, liminf_congr heq]

end CircleDomainRigidity

end OAI
