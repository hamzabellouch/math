import OAI.Analysis.MassAction.FixedMinimum
import OAI.Analysis.MassAction.PolyhedronGeometry

namespace OAI

noncomputable section
namespace Problem326.Affine

/-- The superlevel set of every member of a finite affine family. -/
def labelPolytope {d : ℕ} (Λ : Finset (Label d)) (h M : ℝ) :
    Set (Fin d → ℝ) := {x | ∀ L ∈ Λ, M ≤ L.value h x}

lemma labelPolytope_isFinitePolyhedron {d : ℕ}
    (Λ : Finset (Label d)) (h M : ℝ) : IsFinitePolyhedron (labelPolytope Λ h M) := by
  classical
  have hpoly := finiteAffine_superlevel_isFinitePolyhedron
    (fun L : Λ => L.val.slope) (fun L : Λ => L.val.offset h) M
  convert hpoly using 1
  ext x
  simp only [labelPolytope, Set.mem_ofPred_eq, Subtype.forall, Label.value, dot]

lemma labelPolytope_active_iff {d : ℕ} {Λ : Finset (Label d)}
    {h : ℝ} {L0 L : Label d} {x : Fin d → ℝ}
    (hL0 : L0 ∈ Λ) (hzero : L0.slope = 0)
    (hx : x ∈ labelPolytope Λ h (L0.offset h)) :
    Active Λ L h x ↔ L ∈ Λ ∧ L.value h x = L0.offset h := by
  have hvalue : L0.value h x = L0.offset h := by simp [Label.value, hzero]
  constructor
  · intro ha
    exact ⟨ha.1, le_antisymm (by simpa only [hvalue] using ha.2 L0 hL0) (hx L ha.1)⟩
  · rintro ⟨hL, hLeq⟩
    exact ⟨hL, fun J hJ => hLeq ▸ hx J hJ⟩

/-- The geometric part of the affine trapping construction, with the canonical
label and activity definitions. Only the activity certificates are assumed;
no differential equation or global-solution assertion is used. -/
lemma exists_compact_labelPolytope {d : ℕ}
    (Λ : Finset (Label d)) (hne : Λ.Nonempty) (h : ℝ)
    (B : Set (Fin d → ℝ)) (x0 : Fin d → ℝ)
    (hB : IsCompact B) (hx0B : x0 ∈ interior B)
    (hinitial : ∀ L, Active Λ L h x0 → L.slope = 0)
    (hboundary : ∀ x ∈ frontier B, ∀ L, Active Λ L h x → L.slope ≠ 0) :
    ∃ L0, Active Λ L0 h x0 ∧ L0.slope = 0 ∧
      IsCompact (labelPolytope Λ h (L0.offset h)) ∧
      Convex ℝ (labelPolytope Λ h (L0.offset h)) ∧
      IsFinitePolyhedron (labelPolytope Λ h (L0.offset h)) ∧
      x0 ∈ labelPolytope Λ h (L0.offset h) ∧
      labelPolytope Λ h (L0.offset h) ⊆ interior B := by
  classical
  obtain ⟨L0, hact⟩ := exists_active Λ hne h x0
  have hzero := hinitial L0 hact
  have hpoly := labelPolytope_isFinitePolyhedron Λ h (L0.offset h)
  have hconv := hpoly.convex
  have hvalue : L0.value h x0 = L0.offset h := by simp [Label.value, hzero]
  have hx0 : x0 ∈ labelPolytope Λ h (L0.offset h) := by
    intro L hL
    simpa only [hvalue] using hact.2 L hL
  have hdisjoint : Disjoint (labelPolytope Λ h (L0.offset h)) (frontier B) := by
    rw [Set.disjoint_left]
    intro x hx hxB
    have hactx : Active Λ L0 h x :=
      (labelPolytope_active_iff hact.1 hzero hx).2
        ⟨hact.1, by simp [Label.value, hzero]⟩
    exact hboundary x hxB L0 hactx hzero
  have hsub : labelPolytope Λ h (L0.offset h) ⊆ interior B :=
    Geometry.subset_interior_of_disjoint_frontier hconv.isPreconnected
      ⟨x0, hx0, hx0B⟩ hdisjoint
  have hcompact : IsCompact (labelPolytope Λ h (L0.offset h)) :=
    hB.of_isClosed_subset hpoly.isClosed (hsub.trans interior_subset)
  exact ⟨L0, hact, hzero, hcompact, hconv, hpoly, hx0, hsub⟩

end Problem326.Affine

end

end OAI
