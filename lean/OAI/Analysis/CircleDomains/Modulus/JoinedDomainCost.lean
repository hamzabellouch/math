import OAI.Analysis.CircleDomains.Modulus.JoinedJunctionCost
import OAI.Analysis.CircleDomains.Modulus.InteriorPhysicalCost

namespace OAI

/-! Join two allowed true pieces at a domain point, retaining their
full costs. This is the normalization step between successive jumps. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_allowed_joined_full_cost
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (hm : ∀x ∈ d.quotientDomain, m x = 0)
    (Γ Δ : TaggedPhysicalPath d)
    (hΓ : AllowedTaggedPath d ν N (Γ.1.val, Γ.2))
    (hΔ : AllowedTaggedPath d ν N (Δ.1.val, Δ.2))
    (hΓ0 : Γ.1.val ⊥ ∈ d.quotientDomain) (hΓ1 : Γ.1.val ⊤ ∈ d.quotientDomain)
    (hΔ1 : Δ.1.val ⊤ ∈ d.quotientDomain) (hjoin : Γ.1.val ⊤ = Δ.1.val ⊥)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x) :
    ∃ρ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (ρ.1.val, ρ.2) ∧
      ρ.1.val ⊥ = Γ.1.val ⊥ ∧ ρ.1.val ⊤ = Δ.1.val ⊤ ∧
      physicalTollCost d g m ρ.1 = physicalTollCost d g m Γ.1 + physicalTollCost d g m Δ.1 := by
  obtain ⟨ρ, θ, hρ, hρ0, hρ1, hc⟩ := exists_allowed_joined_junction_cost
    d hU ν N Γ Δ hΓ hΔ hjoin g hg m hpoint
  refine ⟨(ρ, θ), hρ, hρ0, hρ1, ?_⟩
  rw [← interiorPhysicalTollCost_eq_full d g m ρ (hm _ (hρ0.symm ▸ hΓ0))
    (hm _ (hρ1.symm ▸ hΔ1)), hc, hm _ hΓ1, add_zero,
    interiorPhysicalTollCost_eq_full d g m Γ.1 (hm _ hΓ0) (hm _ hΓ1),
    interiorPhysicalTollCost_eq_full d g m Δ.1 (hm _ (hjoin ▸ hΓ1)) (hm _ hΔ1)]

end CircleDomainRigidity

end

end OAI
