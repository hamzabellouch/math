import OAI.Analysis.CircleDomains.Topology.SmallCollarArcs
import OAI.Analysis.CircleDomains.Probability.DomainPhysicalOccupation

namespace OAI

/-! The short physical collar arcs project to allowed tagged quotient
paths, with the same physical cost and zero dust toll. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_small_allowed_collar_arcs
    (d : PathCodeData X Y) (hdisj : Disjoint d.quotientDomain d.dust)
    (ν : Measure X) (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (β : RectifiablePath Y) (hβ : ∀ t, β.val t ∈ d.physicalDomain)
    (g : Y → ℝ≥0∞) (hg : Measurable g)
    (hfinite : (∫⁻ t, g (β.val t) ∂pathLengthMeasure β) < ∞)
    (m : X → ℝ≥0∞) (hm : ∀ x ∈ d.quotientDomain, m x = 0)
    (r : PathTime) (hsingle : ∀ s, β.val s = β.val r → s = r)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ V : Set Y, IsOpen V ∧ β.val r ∈ V ∧
      ∀ a b : PathTime, β.val a ∈ V → β.val b ∈ V →
        ∃ ρ : FinitePhysicalPath d.domainEquiv d.basePoint,
          AllowedTaggedPath d ν N (ρ.val, fun _ => inactiveTag) ∧
          ρ.val ⊥ = projectDomainPath d.domainEquiv β.val hβ a ∧
          ρ.val ⊤ = projectDomainPath d.domainEquiv β.val hβ b ∧
          range ρ.val ⊆ range (projectDomainPath d.domainEquiv β.val hβ) ∧
          (∫⁻ y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ) < ε ∧
          boundaryToll ρ.val m = 0 := by
  obtain ⟨V, hV, hrV, hsmall⟩ := exists_small_collar_arcs β g hg hfinite r hsingle hε
  refine ⟨V, hV, hrV, fun a b ha hb => ?_⟩
  obtain ⟨α, hα0, hα1, hαrange, hαcost⟩ := hsmall (β.val a) ⟨ha, mem_range_self a⟩
    (β.val b) ⟨hb, mem_range_self b⟩
  have hα : ∀ t, α.val t ∈ d.physicalDomain := by
    intro t
    obtain ⟨s, hs⟩ := hαrange (mem_range_self t)
    exact hs ▸ hβ s
  let ρ := finiteProjectedPhysicalPath d.domainEquiv d.basePoint α hα
  refine ⟨ρ, projected_physical_path_allowed d hdisj ν N α hα, ?_, ?_, ?_, ?_, ?_⟩
  · apply congrArg Subtype.val
    apply congrArg d.domainEquiv
    exact Subtype.ext hα0
  · apply congrArg Subtype.val
    apply congrArg d.domainEquiv
    exact Subtype.ext hα1
  · rintro x ⟨t, rfl⟩
    obtain ⟨s, hs⟩ := hαrange (mem_range_self t)
    refine ⟨s, ?_⟩
    apply congrArg Subtype.val
    apply congrArg d.domainEquiv
    exact Subtype.ext hs
  · change (∫⁻ y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint
      (finiteProjectedPhysicalPath d.domainEquiv d.basePoint α hα)) < ε
    rwa [dyadicPhysicalOccupation_project]
  · change (∑' t, m (projectDomainPath d.domainEquiv α.val hα t)) = 0
    apply ENNReal.tsum_eq_zero.mpr
    intro t
    exact hm _ (projectDomainPath_mem d.domainEquiv α.val hα t)

end CircleDomainRigidity

end

end OAI
