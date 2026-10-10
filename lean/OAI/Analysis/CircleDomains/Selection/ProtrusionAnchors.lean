import OAI.Analysis.CircleDomains.Selection.ProtrusionTestGeometry
import OAI.Analysis.CircleDomains.Topology.AnchoredMeanCollars

namespace OAI

/-! Compact nested endpoint anchors retain the actual protrusion test anchor
and the normalized point at infinity, while remaining inside the quotient domain. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem FiniteTransfer.LocalEndTestGeometry.exists_endpoint_anchors
    {S : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
    {M : RealModelExhaustion d O ε} {A : AssignedRealModelLimit M} {q : Sphere}
    {E : RealTargetEnd A q} (T : LocalEndTestGeometry E)
    (hU : IsOpen U) (hπ : Continuous π) (e : G ≃ₜ U)
    (he : ∀ x : G, (e x).val = π x.val) :
    ∃ EStar Anchor : Set Sphere, IsCompact EStar ∧ IsClosed Anchor ∧
      EStar ⊆ interior Anchor ∧ Anchor ⊆ U ∧
      π OnePoint.infty ∈ interior EStar ∧
      (∀ z ∈ closure (jordanInterior T.sourceAnchor), π (z : Sphere) ∈ EStar) := by
  have hinfty : OnePoint.infty ∈ G := M.core_source 0 (M.plane_core 0 (Or.inr rfl))
  let K : Set Sphere := {π OnePoint.infty} ∪
    π '' (((↑) : ℂ → Sphere) '' closure (jordanInterior T.sourceAnchor))
  have hK : IsCompact K := isCompact_singleton.union
    (((isCompact_closure_jordanInterior T.sourceAnchor).image OnePoint.continuous_coe).image hπ)
  have hKU : K ⊆ U := by
    rintro x (hx | ⟨_, ⟨z, hz, rfl⟩, rfl⟩)
    · rw [mem_singleton_iff] at hx
      rw [hx, ← he ⟨_, hinfty⟩]
      exact (e ⟨_, hinfty⟩).property
    · rw [← he ⟨_, T.source_inside hz⟩]
      exact (e ⟨_, T.source_inside hz⟩).property
  obtain ⟨EStar, hcompact, _, hKE, hEU⟩ := exists_compact_closed_between hK hU hKU
  obtain ⟨Anchor, _, hclosed, hEA, hAU⟩ := exists_compact_closed_between hcompact hU hEU
  refine ⟨EStar, Anchor, hcompact, hclosed, hEA, hAU, hKE (Or.inl rfl), ?_⟩
  intro z hz
  exact interior_subset (hKE (Or.inr ⟨_, ⟨z, hz, rfl⟩, rfl⟩))

 theorem FiniteTransfer.LocalEndTestGeometry.exists_endpoint_anchors_retaining
    {S : Type*} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
    {M : RealModelExhaustion d O ε} {A : AssignedRealModelLimit M} {q : Sphere}
    {E : RealTargetEnd A q} (T : LocalEndTestGeometry E)
    (hU : IsOpen U) (hπ : Continuous π) (e : G ≃ₜ U)
    (he : ∀ x : G, (e x).val = π x.val)
    (E₀ : Set Sphere) (hE₀ : IsCompact E₀) (hE₀U : E₀ ⊆ U) :
    ∃ EStar Anchor : Set Sphere, IsCompact EStar ∧ IsClosed Anchor ∧
      EStar ⊆ interior Anchor ∧ Anchor ⊆ U ∧
      E₀ ⊆ interior EStar ∧ π OnePoint.infty ∈ interior EStar ∧
      (∀ z ∈ closure (jordanInterior T.sourceAnchor), π (z : Sphere) ∈ EStar) := by
  obtain ⟨E₁, A₁, hE₁, _, hE₁A₁, hA₁U, hinfty1, hsource⟩ :=
    T.exists_endpoint_anchors hU hπ e he
  have hE₁U : E₁ ⊆ U := fun x hx => hA₁U (interior_subset (hE₁A₁ hx))
  obtain ⟨EStar, hcompact, _, hKE, hEU⟩ :=
    exists_compact_closed_between (hE₀.union hE₁) hU (union_subset hE₀U hE₁U)
  obtain ⟨Anchor, _, hclosed, hEA, hAU⟩ := exists_compact_closed_between hcompact hU hEU
  refine ⟨EStar, Anchor, hcompact, hclosed, hEA, hAU,
    (fun _ hx => hKE (Or.inl hx)), hKE (Or.inr (interior_subset hinfty1)), ?_⟩
  intro z hz
  exact interior_subset (hKE (Or.inr (hsource z hz)))

end CircleDomainRigidity

end

end OAI
