import Mathlib

namespace OAI

universe uX

open Set

namespace Problem326

/-- A continuous curve cannot first leave a closed region if every initial segment
inside the region ends in a fixed subset of its interior. -/
theorem mapsTo_interior_of_initial_segments {X : Type uX} [TopologicalSpace X]
    {x : ℝ → X} {a b : ℝ} {B K : Set X}
    (hB : IsClosed B) (hK : K ⊆ interior B)
    (hc : ContinuousOn x (Icc a b)) (ha : x a ∈ interior B)
    (htrap : ∀ t ∈ Icc a b, MapsTo x (Icc a t) B → x t ∈ K) :
    MapsTo x (Icc a b) (interior B) := by
  intro t ht
  by_contra hxt
  let S := Icc a b ∩ x ⁻¹' (interior B)ᶜ
  have hS : IsClosed S :=
    hc.preimage_isClosed_of_isClosed isClosed_Icc isOpen_interior.isClosed_compl
  have hSne : S.Nonempty := ⟨t, ht, hxt⟩
  have hSbelow : BddBelow S := ⟨a, fun u hu => hu.1.1⟩
  obtain ⟨hτ, hleast⟩ := hS.isLeast_csInf hSne hSbelow
  let τ := sInf S
  have hτab : τ ∈ Icc a b := hτ.1
  have hτbad : x τ ∉ interior B := hτ.2
  have haτ : a < τ := by
    apply lt_of_le_of_ne hτab.1
    intro he
    exact hτbad (he ▸ ha)
  have hgood : Ico a τ ⊆ Icc a b ∩ x ⁻¹' B := by
    intro u hu
    have huab : u ∈ Icc a b := ⟨hu.1, hu.2.le.trans hτab.2⟩
    refine ⟨huab, ?_⟩
    change x u ∈ B
    apply interior_subset
    by_contra hxu
    have huS : u ∈ S := ⟨huab, hxu⟩
    exact (not_le_of_gt hu.2) (hleast huS)
  have hclosed : IsClosed (Icc a b ∩ x ⁻¹' B) :=
    hc.preimage_isClosed_of_isClosed isClosed_Icc hB
  have hsegment : Icc a τ ⊆ Icc a b ∩ x ⁻¹' B := by
    rw [← closure_Ico haτ.ne]
    exact closure_minimal hgood hclosed
  have hτK : x τ ∈ K := htrap τ hτab (fun u hu => (hsegment hu).2)
  exact hτbad (hK hτK)

/-- Endpoint trapping on every initial segment upgrades to trapping on the entire
closed interval once the trapping set lies strictly inside the closed region. -/
theorem mapsTo_of_initial_segments {X : Type uX} [TopologicalSpace X]
    {x : ℝ → X} {a b : ℝ} {B K : Set X}
    (hB : IsClosed B) (hK : K ⊆ interior B)
    (hc : ContinuousOn x (Icc a b)) (ha : x a ∈ interior B)
    (htrap : ∀ t ∈ Icc a b, MapsTo x (Icc a t) B → x t ∈ K) :
    MapsTo x (Icc a b) K := by
  have hint := mapsTo_interior_of_initial_segments hB hK hc ha htrap
  intro t ht
  apply htrap t ht
  intro u hu
  exact interior_subset (hint ⟨hu.1, hu.2.trans ht.2⟩)

end Problem326

end OAI
