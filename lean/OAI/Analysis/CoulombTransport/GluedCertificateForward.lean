import OAI.Analysis.CoulombTransport.GluedCertificate

namespace OAI

universe uIndex

noncomputable section
open Set Filter Metric
open scoped ENNReal BigOperators

namespace Problem356

/-- The finite gluing construction only needs forward contact localization.
The explicit contact candidates may be shown saturated separately, so no
converse from the chosen global contact predicate is required here. -/
theorem exists_glued_component_certificate_forward {ι : Type uIndex} [Fintype ι]
    (p : ι → E3) (hp : Function.Injective p)
    (V : ι → Set E3) (hV : ∀ i, IsOpen (V i)) (hpV : ∀ i, p i ∈ V i)
    (v : ι → E3 → ℝ) (hv : ∀ i, ContinuousOn (v i) (V i))
    (Good : (ι × (ι × ι)) → Prop) (Contact : Triple → Prop)
    (hgood : ∀ a, Good a → ∀ᶠ t in nhds (p a.1, (p a.2.1, p a.2.2)),
      ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) ≤ coulombCost t ∧
      (ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) =
        coulombCost t → Contact t))
    (hbad : ∀ a, ¬ Good a →
      ENNReal.ofReal (v a.1 (p a.1) + v a.2.1 (p a.2.1) + v a.2.2 (p a.2.2)) <
        coulombCost (p a.1, (p a.2.1, p a.2.2))) :
    ∃ r M : ℝ, 0 < r ∧ 0 < M ∧
      let U := fun i => ball (p i) r
      let u := ComponentPotential.glue U v
      (∀ i, U i ⊆ V i) ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) ∧
      Measurable u ∧ ContinuousOn u (⋃ i, U i) ∧ (∀ x, |u x| ≤ M) ∧
      (∀ x ∈ ⋃ i, U i, ∀ y ∈ ⋃ i, U i, ∀ z ∈ ⋃ i, U i,
        ENNReal.ofReal (u x + u y + u z) ≤ coulombCost (x, (y, z)) ∧
        (ENNReal.ofReal (u x + u y + u z) = coulombCost (x, (y, z)) →
          Contact (x, (y, z)))) := by
  let C : (ι × (ι × ι)) → Triple → Prop := fun a t =>
    ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) = coulombCost t ∧
      Contact t
  have hgood' : ∀ a, Good a → ∀ᶠ t in nhds (p a.1, (p a.2.1, p a.2.2)),
      ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) ≤ coulombCost t ∧
      (ENNReal.ofReal (v a.1 t.1 + v a.2.1 t.2.1 + v a.2.2 t.2.2) =
        coulombCost t ↔ C a t) := by
    intro a ha
    filter_upwards [hgood a ha] with t ht
    exact ⟨ht.1, ⟨fun heq => ⟨heq, ht.2 heq⟩, fun hc => hc.1⟩⟩
  obtain ⟨r, M, hr, hM, hUV, hdisj, hmeas, hcont, hbound, hcert⟩ :=
    exists_glued_component_certificate p hp V hV hpV v hv Good C hgood' hbad
  refine ⟨r, M, hr, hM, hUV, hdisj, hmeas, hcont, hbound, ?_⟩
  intro x hx y hy z hz
  have hc := hcert x hx y hy z hz
  refine ⟨hc.1, ?_⟩
  intro heq
  obtain ⟨a, _, _, _, _, hcontact⟩ := hc.2.mp heq
  exact hcontact.2

end Problem356

end

end OAI
