import OAI.Analysis.CircleDomains.Topology.ClosedRelationNeighborhood
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas

namespace OAI

/-! A closed compact-valued relation with connected fibers has the
intermediate-value property over a connected source. This is the
interval coverage needed for the finite-hole slice estimate. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem closed_relation_intermediate_value
    {X Y : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    [TopologicalSpace Y] [CompactSpace Y]
    {R : X → Y → Prop} (hR : IsClosed {p : X × Y | R p.1 p.2})
    (hne : ∀ x, ∃ y, R x y)
    (hfiber : ∀ x, IsPreconnected {y | R x y})
    {φ : Y → ℝ} (hφ : Continuous φ)
    {x₀ x₁ : X} {y₀ y₁ : Y} (h₀ : R x₀ y₀) (h₁ : R x₁ y₁)
    {t : ℝ} (ht₀ : φ y₀ ≤ t) (ht₁ : t ≤ φ y₁) :
    ∃ x y, R x y ∧ φ y = t := by
  by_contra hnot
  have hne_t (x : X) (y : Y) (hy : R x y) : φ y ≠ t :=
    fun he => hnot ⟨x,y,hy,he⟩
  let A := {x | ∀ y, R x y → φ y < t}
  let B := {x | ∀ y, R x y → t < φ y}
  have hopen (U : Set ℝ) (hU : IsOpen U) :
      IsOpen {x | ∀ y, R x y → φ y ∈ U} := by
    apply isOpen_iff_forall_mem_open.mpr
    intro x hx
    obtain ⟨V,hV,hxV,hmap⟩ := closed_relation_neighborhood (K := {x}) hR (hU.preimage hφ) (by
      intro z hz y hzy
      have he := mem_singleton_iff.mp hz
      subst z
      exact hx y hzy)
    exact ⟨V,fun z hz y hzy => hmap z hz y hzy,hV,hxV (mem_singleton x)⟩
  have hA : IsOpen A := hopen (Iio t) isOpen_Iio
  have hB : IsOpen B := hopen (Ioi t) isOpen_Ioi
  have hcover : (univ : Set X) ⊆ A ∪ B := by
    intro x _
    obtain ⟨p,hp⟩ := hne x
    have hc := ((hfiber x).image φ hφ.continuousOn).ordConnected
    rcases lt_or_gt_of_ne (hne_t x p hp) with hpt | htp
    · left
      intro q hq
      apply lt_of_not_ge
      intro htq
      obtain ⟨z,hz,hzt⟩ := hc.out (mem_image_of_mem φ hp) (mem_image_of_mem φ hq) ⟨hpt.le,htq⟩
      exact hne_t x z hz hzt
    · right
      intro q hq
      apply lt_of_not_ge
      intro hqt
      obtain ⟨z,hz,hzt⟩ := hc.out (mem_image_of_mem φ hq) (mem_image_of_mem φ hp) ⟨hqt,htp.le⟩
      exact hne_t x z hz hzt
  have hdisj : Disjoint A B := by
    apply disjoint_left.mpr
    intro x hxA hxB
    obtain ⟨y,hy⟩ := hne x
    exact (not_lt_of_ge (hxA y hy).le) (hxB y hy)
  rcases isPreconnected_univ.subset_or_subset hA hB hdisj hcover with ha | hb
  · exact (not_lt_of_ge ht₁) (ha (mem_univ x₁) y₁ h₁)
  · exact (not_lt_of_ge ht₀) (hb (mem_univ x₀) y₀ h₀)

end CircleDomainRigidity

end

end OAI
