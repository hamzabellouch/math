import OAI.Analysis.CircleDomains.Modulus.WeightedCollarNeighborhoods

namespace OAI

/-! Strictly nested actual weighted collars, chosen inside any prescribed
sequence of quotient neighborhoods. -/

open Set Function MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem exists_nested_weighted_collars
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    {B : Set Sphere} (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀x ∈ Gᶜ, π x ∈ B) {p : Sphere} (hpB : p ∈ B) (hp : p ≠ π OnePoint.infty)
    (O : ℕ → Set Sphere) (hO : ∀n, IsOpen (O n)) (hpO : ∀n, p ∈ O n)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) (hg2 : (∫⁻z, g z ^ 2) < ∞) :
    ∃ D : ℕ → WeightedCollar G π B p g,
      (∀n, closure (D n).region ⊆ O n) ∧
      (∀n, closure (D (n+1)).region ⊆ (D n).region) ∧
      (∀n, {z | (D n).function z = (D n).level} ⊆
        (fun z : ℂ => π (z : Sphere)) ⁻¹' O n) ∧
      (∀n, {z | (D (n+1)).function z = (D (n+1)).level} ⊆
        (fun z : ℂ => π (z : Sphere)) ⁻¹' (D n).region) := by
  classical
  obtain ⟨D0, hD0, hL0⟩ := exists_weighted_collar_in_neighborhood hcoarea hsard hsch
    G π hπ hclosed hsurj hr hB hTD hbad hpB hp (hO 0) (hpO 0) g hg hg2
  have hstep : ∀ (n : ℕ) (D : WeightedCollar G π B p g),
      ∃ E : WeightedCollar G π B p g,
        closure E.region ⊆ D.region ∩ O (n+1) ∧
        {z | E.function z = E.level} ⊆
          (fun z : ℂ => π (z : Sphere)) ⁻¹' (D.region ∩ O (n+1)) := by
    intro n D
    exact exists_weighted_collar_in_neighborhood hcoarea hsard hsch
      G π hπ hclosed hsurj hr hB hTD hbad hpB hp
      ((D.isOpen_region hπ hclosed hsurj hr).inter (hO (n+1)))
      ⟨D.point_mem_region hsurj hp, hpO (n+1)⟩ g hg hg2
  choose step hstep using hstep
  let D : ℕ → WeightedCollar G π B p g := Nat.rec D0 step
  have hs (n : ℕ) : D (n+1) = step n (D n) := rfl
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · intro n
    cases n with
    | zero => exact hD0
    | succ n => exact fun z hz => ((hstep n (D n)).1 hz).2
  · intro n z hz
    exact ((hstep n (D n)).1 hz).1
  · intro n
    cases n with
    | zero => exact hL0
    | succ n => exact fun z hz => ((hstep n (D n)).2 hz).2
  · intro n z hz
    exact ((hstep n (D n)).2 hz).1

end CircleDomainRigidity

end

end OAI
