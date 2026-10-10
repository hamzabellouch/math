import OAI.Analysis.CircleDomains.Modulus.ShrinkingWeightedCollars

namespace OAI

/-! Choose all prescribed shrinking collars outside the fixed anchor.
The zero-weight specialization needs only the published geometric inputs. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric

theorem exists_anchored_collar_family
    (hcoarea : WeightedPlanarScalarCoarea) (hsard : SmoothPlanarSard)
    (hsch : PlanarSchoenflies)
    (G : Set Sphere) (π : Sphere → Sphere) (hπ : Continuous π)
    (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (B : Set Sphere) (hB : IsClosed B) (hTD : IsTotallyDisconnected B)
    (hbad : ∀ x ∈ Gᶜ, π x ∈ B) (hinfty : π OnePoint.infty ∉ B)
    (E : Set Sphere) (hE : IsClosed E) (hEB : Disjoint E B) :
    ∃ D : ∀ p : B, ℕ → WeightedCollar G π B p.val (fun _ => 0),
      (∀ p n, closure (D p (n + 1)).region ⊆ (D p n).region) ∧
      (∀ p : B, ∀ V ∈ 𝓝 p.val, ∃ k : ℕ, ∀ n ≥ k, closure (D p n).region ⊆ V) ∧
      ∀ p, Disjoint E (closure (D p 0).region) := by
  have hex (p : B) := exists_shrinking_weighted_collars hcoarea hsard hsch
    G π hπ hclosed hsurj hr hB hTD hbad p.property
    (fun h => hinfty (h ▸ p.property)) hE.isOpen_compl
    (fun h => disjoint_left.mp hEB h p.property) (fun _ => 0) measurable_const
    (by simp)
  choose D hD0 hnest _ hshrink using hex
  refine ⟨D, hnest, ?_, ?_⟩
  · intro p V hV
    obtain ⟨k, hk⟩ := hshrink p V hV
    exact ⟨k, fun n hn => (hk n hn).1⟩
  · intro p
    apply disjoint_left.mpr
    intro x hxE hxD
    exact hD0 p hxD hxE

end CircleDomainRigidity

end

end OAI
