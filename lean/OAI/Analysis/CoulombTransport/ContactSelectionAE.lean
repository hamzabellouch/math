import Mathlib

namespace OAI

universe uAlpha uIndex

/-!
# From permuted contact triples to deterministic branch selection

The central component is disjoint from every outer branch image. Therefore,
when a contact triple is written with its first coordinate in the central
component, its second coordinate must be an outer branch of that same point.
The statements are independent of the analytic construction of the branches.
-/

open MeasureTheory
open scoped ENNReal

namespace Problem356.ContactSelection

variable {α : Type uAlpha} {ι : Type uIndex}

/-- A deliberately broad contact relation: any pair of outer branches is
allowed. A more precise geometric contact set can imply this relation. -/
def BranchContact (B : Set α) (H : ι → α → α) (t : α × (α × α)) : Prop :=
  ∃ x ∈ B, ∃ i j, List.Perm [t.1, t.2.1, t.2.2] [x, H i x, H j x]

/-- Removing the unique central entry of a permuted triple leaves two outer
entries. Neither injectivity nor pairwise disjointness of the outer images
is required for this step. -/
theorem second_eq_outer_of_perm {B : Set α} {a b c x y z : α}
    (ha : a ∈ B) (hy : y ∉ B) (hz : z ∉ B)
    (hp : List.Perm [a, b, c] [x, y, z]) : b = y ∨ b = z := by
  have ha' : a = x ∨ a = y ∨ a = z := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using
      (hp.mem_iff.mp (by simp : a ∈ [a, b, c]))
  have hax : a = x := ha'.resolve_right (by
    rintro (h | h)
    · exact hy (h ▸ ha)
    · exact hz (h ▸ ha))
  subst x
  have hp' : List.Perm [b, c] [y, z] := List.Perm.cons_inv hp
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using
    (hp'.mem_iff.mp (by simp : b ∈ [b, c]))

theorem second_selects_of_contact {B : Set α} {H : ι → α → α}
    (houter : ∀ i x, x ∈ B → H i x ∉ B)
    {t : α × (α × α)} (hfirst : t.1 ∈ B) (hcontact : BranchContact B H t) :
    ∃ i, t.2.1 = H i t.1 := by
  rcases hcontact with ⟨x, hx, i, j, hp⟩
  have hm : t.1 = x ∨ t.1 = H i x ∨ t.1 = H j x := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using
      (hp.mem_iff.mp (by simp : t.1 ∈ [t.1, t.2.1, t.2.2]))
  have hcentral : t.1 = x := hm.resolve_right (by
    rintro (h | h)
    · exact houter i x hx (h ▸ hfirst)
    · exact houter j x hx (h ▸ hfirst))
  rcases second_eq_outer_of_perm hfirst (houter i x hx) (houter j x hx) hp with h | h
  · exact ⟨i, h.trans (congrArg (H i) hcentral.symm)⟩
  · exact ⟨j, h.trans (congrArg (H j) hcentral.symm)⟩

theorem second_selects_of_contact_disjoint {B : Set α} {H : ι → α → α}
    (houter : ∀ i, Disjoint B (H i '' B))
    {t : α × (α × α)} (hfirst : t.1 ∈ B) (hcontact : BranchContact B H t) :
    ∃ i, t.2.1 = H i t.1 := by
  apply second_selects_of_contact (B := B) (H := H) ?_ hfirst hcontact
  intro i x hx hix
  exact Set.disjoint_left.mp (houter i) hix ⟨x, hx, rfl⟩

variable [MeasurableSpace α]

/-- Transfer the contact relation from the marginal to a central component
measure, and then extract the branch selected by the second graph map. -/
theorem ae_selects_of_ae_contact {μ ν : Measure α} {B : Set α}
    {H : ι → α → α} {T₂ T₃ : α → α}
    (hac : ν ≪ μ) (hB : ∀ᵐ x ∂ν, x ∈ B)
    (houter : ∀ i, Disjoint B (H i '' B))
    (hcontact : ∀ᵐ x ∂μ, BranchContact B H (x, (T₂ x, T₃ x))) :
    ∀ᵐ x ∂ν, ∃ i, T₂ x = H i x := by
  filter_upwards [hB, hac.ae_le hcontact] with x hx hc
  exact second_selects_of_contact_disjoint houter hx hc

/-- A positive-weight component is absolutely continuous with respect to any
measure dominating it, including the five-component branch mixture. -/
theorem absolutelyContinuous_of_smul_le {μ ν : Measure α} {a : ℝ≥0∞}
    (ha : a ≠ 0) (hdom : a • ν ≤ μ) : ν ≪ μ :=
  (Measure.absolutelyContinuous_smul ha).trans hdom.absolutelyContinuous

theorem ae_selects_of_smul_le_of_ae_contact {μ ν : Measure α} {a : ℝ≥0∞}
    {B : Set α} {H : ι → α → α} {T₂ T₃ : α → α}
    (ha : a ≠ 0) (hdom : a • ν ≤ μ) (hB : ∀ᵐ x ∂ν, x ∈ B)
    (houter : ∀ i, Disjoint B (H i '' B))
    (hcontact : ∀ᵐ x ∂μ, BranchContact B H (x, (T₂ x, T₃ x))) :
    ∀ᵐ x ∂ν, ∃ i, T₂ x = H i x :=
  ae_selects_of_ae_contact (absolutelyContinuous_of_smul_le ha hdom) hB houter hcontact

end Problem356.ContactSelection

end OAI
