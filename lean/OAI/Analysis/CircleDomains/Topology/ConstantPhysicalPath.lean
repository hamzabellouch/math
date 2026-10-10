import OAI.Analysis.CircleDomains.Topology.DomainPhysicalPaths
import OAI.Analysis.CircleDomains.Topology.RectifiableSubarcs
import OAI.Analysis.CircleDomains.Modulus.InterleavedCollarCost

namespace OAI

/-! A constant path at a domain point is allowed and has zero cost. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_allowed_constant_physical_path
    (d : PathCodeData X Y) (hdisj : Disjoint d.quotientDomain d.dust)
    (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    {x : X} (hx : x ∈ d.quotientDomain) (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (hm : m x = 0) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ (∀t, ρ.val t = x) ∧
      physicalTollCost d g m ρ = 0 := by
  let y := d.domainEquiv.symm ⟨x, hx⟩
  let β := constantRectifiablePath y.val
  have hβ (t : PathTime) : β.val t ∈ d.physicalDomain := y.property
  let γ := projectDomainPath d.domainEquiv β.val hβ
  have hγ (t : PathTime) : γ t = x := by
    change (d.domainEquiv y).val = x
    exact congrArg Subtype.val (d.domainEquiv.apply_symm_apply ⟨x, hx⟩)
  have hlen : physicalDomainLength d.domainEquiv d.basePoint γ = 0 := by
    rw [physicalDomainLength_project d.domainEquiv d.basePoint β hβ]
    exact (eVariationOn.eq_zero_iff _).mpr fun _ _ _ _ => edist_self _
  let ρ : FinitePhysicalPath d.domainEquiv d.basePoint := ⟨γ, by rw [hlen]; exact ENNReal.zero_lt_top⟩
  have hocc : dyadicPhysicalOccupation d.domainEquiv d.basePoint ρ = 0 := by
    apply Measure.measure_univ_eq_zero.mp
    rw [dyadicPhysicalOccupation_univ]
    exact hlen
  refine ⟨ρ, fun _ => inactiveTag,
    projected_physical_path_allowed d hdisj ν N β hβ, hγ, ?_⟩
  unfold physicalTollCost
  rw [hocc, lintegral_zero_measure, zero_add]
  change (∑'t : PathTime, m (γ t)) = 0
  simp only [hγ, hm, tsum_zero]

end CircleDomainRigidity

end

end OAI
