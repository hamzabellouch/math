import OAI.Analysis.CircleDomains.Modulus.ShrinkingWeightedCollars

namespace OAI

/-! The actual nested collars for a finite marked point can simultaneously
avoid the closed source anchor and the quotient point at infinity. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric

 theorem exists_anchored_shrinking_weighted_collars
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (G U B E : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hB : IsClosed B) (hTD : IsTotallyDisconnected B) (hdisj : Disjoint U B)
    (hbad : ∀ x ∈ Gᶜ, π x ∈ B) (hE : IsClosed E) (hEU : E ⊆ U)
    (hinfty : π OnePoint.infty ∉ B) {p : Sphere} (hpB : p ∈ B) (hp : p ≠ OnePoint.infty) :
    ∃ D : ℕ → WeightedCollar G π B p (fun _ => 0),
      (∀ n, closure (D (n+1)).region ⊆ (D n).region) ∧
      (∀ W ∈ 𝓝 p, ∃ k : ℕ, ∀ n ≥ k, closure (D n).region ⊆ W) ∧
      Disjoint E (closure (D 0).region) ∧ OnePoint.infty ∉ closure (D 0).region := by
  have hpE : p ∉ E := fun hx => disjoint_left.mp hdisj (hEU hx) hpB
  have hpi : p ≠ π OnePoint.infty := fun h => hinfty (h ▸ hpB)
  obtain ⟨D, hD, hnest, _, hshrink⟩ := exists_shrinking_weighted_collars
    hcoarea hsard hsch G π hπ hclosed hsurj hr hB hTD hbad hpB hpi
    (hE.isOpen_compl.inter isClosed_singleton.isOpen_compl) ⟨hpE, hp⟩
    (fun _ => 0) measurable_const (by simp)
  refine ⟨D, hnest, (fun W hW => by
    obtain ⟨k, hk⟩ := hshrink W hW
    exact ⟨k, fun n hn => (hk n hn).1⟩), disjoint_left.mpr ?_, ?_⟩
  · intro x hxE hxD
    exact (hD hxD).1 hxE
  · intro hx
    exact (hD hx).2 rfl

end CircleDomainRigidity

end

end OAI
