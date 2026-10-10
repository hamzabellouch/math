import OAI.Geometry.NodalSets.Elliptic.EnvelopeNestedDomainsLemmas

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

theorem local_envelope_nested_domains (S S0 : Coord → ℝ)
    {P B C : Set Coord} (hP : IsOpen P) (hPc : IsCompact (closure P))
    (hB : IsOpen B) (hPB : closure P ⊆ B)
    (hS : ContDiffOn ℝ ∞ S B) (hS0 : ContDiffOn ℝ ∞ S0 B)
    (hC : IsCompact C) (hCP : C ⊆ P) {d : ℝ} (hd : 0 < d)
    (hgap : ∀ x ∈ P, x ∉ C → S x ≤ S0 x-d) :
    ∃ U Ω : Set Coord, IsOpen U ∧ IsOpen Ω ∧ C ⊆ U ∧
      IsCompact (closure U) ∧ closure U ⊆ Ω ∧
      IsCompact (closure Ω) ∧ closure Ω ⊆ P ∧
      IsCompact {x | x ∈ P ∧ S0 x-d/2 ≤ S x} ∧
      {x | x ∈ P ∧ S0 x-d/2 ≤ S x} ⊆ U ∧
      (∀ x ∈ P, x ∉ U → S x ≤ S0 x-d) := by
  obtain ⟨R,hR,hRc,hRB,hRe⟩ := compact_smooth_extension hPc hB hPB S hS
  obtain ⟨R0,hR0,hR0c,hR0B,hR0e⟩ := compact_smooth_extension hPc hB hPB S0 hS0
  have hReq (x : Coord) (hx : x ∈ P) : R x = S x := (hRe x (subset_closure hx)).eq_of_nhds
  have hR0eq (x : Coord) (hx : x ∈ P) : R0 x = S0 x := (hR0e x (subset_closure hx)).eq_of_nhds
  have hg : ∀ x ∈ P, x ∉ C → R x ≤ R0 x-d := by
    intro x hx hxc
    rw [hReq x hx,hR0eq x hx]
    exact hgap x hx hxc
  obtain ⟨hQ,hQC⟩ := compact_high_envelope_set R R0 hR.continuous hR0.continuous hC hCP hd hg
  have he : {x | x ∈ P ∧ R0 x-d/2 ≤ R x} = {x | x ∈ P ∧ S0 x-d/2 ≤ S x} := by
    ext x
    by_cases hx : x ∈ P
    · simp only [mem_ofPred_eq,hx,true_and,hReq x hx,hR0eq x hx]
    · simp [hx]
  rw [he] at hQ hQC
  obtain ⟨U,Ω,hU,hΩ,hCU,hUc,hUΩ,hΩc,hΩP⟩ := envelope_nested_domains hC hP hCP
  exact ⟨U,Ω,hU,hΩ,hCU,hUc,hUΩ,hΩc,hΩP,hQ,hQC.trans hCU,
    fun x hx hxU ↦ hgap x hx (fun hc ↦ hxU (hCU hc))⟩

end
end Yau.Geometry

end OAI
