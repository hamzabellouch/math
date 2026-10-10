import OAI.Analysis.CircleDomains.Modulus.RegularJordanNormalSides

namespace OAI

/-! Connectedness makes the inward choice of the actual normal field
constant around a regular Jordan circuit. -/
open Set Function Metric Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma regular_jordan_global_normal_side
    {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : RegularJordanParametrization H γ) :
    ∃ positive : Bool, ∀ t : ℝ, ∃ r > 0, ∀ ρ ∈ Ioo (0 : ℝ) r,
      if positive then
        curveNormalStrip γ (t,ρ) ∈ jordanInterior H ∧
          curveNormalStrip γ (t,-ρ) ∈ (closure (jordanInterior H))ᶜ
      else
        curveNormalStrip γ (t,-ρ) ∈ jordanInterior H ∧
          curveNormalStrip γ (t,ρ) ∈ (closure (jordanInterior H))ᶜ := by
  let S : Bool → Set ℝ := fun b => {x | ∃ t r, 0 < r ∧
    NormalSidePattern H γ t r b ∧ x ∈ Ioo (t-r) (t+r)}
  have ho (b : Bool) : IsOpen (S b) := by
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨t,r,hr,hp,hx⟩
    exact Filter.mem_of_superset (isOpen_Ioo.mem_nhds hx)
      (fun y hy => ⟨t,r,hr,hp,hy⟩)
  have hd : Disjoint (S true) (S false) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨t,r,hr,hp,hx⟩ ⟨u,s,hs,hn,hy⟩
    obtain ⟨ρ,hρ0,hρ⟩ := exists_between (lt_min hr hs)
    have hρr : ρ < r := hρ.trans_le (min_le_left _ _)
    have hρs : ρ < s := hρ.trans_le (min_le_right _ _)
    have hi : curveNormalStrip γ (x,ρ) ∈ jordanInterior H := (hp x hx ρ ⟨hρ0,hρr⟩).1
    have he : curveNormalStrip γ (x,ρ) ∈ (closure (jordanInterior H))ᶜ :=
      (hn x hy ρ ⟨hρ0,hρs⟩).2
    exact he (subset_closure hi)
  have hc : (univ : Set ℝ) ⊆ S true ∪ S false := by
    intro t _
    obtain ⟨r,hr,hp | hn⟩ := exists_local_normal_side_pattern hγ t
    · exact Or.inl ⟨t,r,hr,hp,by constructor <;> linarith⟩
    · exact Or.inr ⟨t,r,hr,hn,by constructor <;> linarith⟩
  have hall : (univ : Set ℝ) ⊆ S true ∨ (univ : Set ℝ) ⊆ S false :=
    isPreconnected_univ.subset_or_subset (ho true) (ho false) hd hc
  have hfinish (b : Bool) (hb : (univ : Set ℝ) ⊆ S b) :
      ∀ t : ℝ, ∃ r > 0, ∀ ρ ∈ Ioo (0 : ℝ) r,
        if b then
          curveNormalStrip γ (t,ρ) ∈ jordanInterior H ∧
            curveNormalStrip γ (t,-ρ) ∈ (closure (jordanInterior H))ᶜ
        else
          curveNormalStrip γ (t,-ρ) ∈ jordanInterior H ∧
            curveNormalStrip γ (t,ρ) ∈ (closure (jordanInterior H))ᶜ := by
    intro t
    obtain ⟨u,r,hr,hp,ht⟩ := hb (mem_univ t)
    exact ⟨r,hr,hp t ht⟩
  rcases hall with h | h
  · exact ⟨true,hfinish true h⟩
  · exact ⟨false,hfinish false h⟩

end CircleDomainRigidity

end

end OAI
