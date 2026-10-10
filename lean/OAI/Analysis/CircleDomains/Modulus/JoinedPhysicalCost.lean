import OAI.Analysis.CircleDomains.Topology.JoinedAllowedPaths
import OAI.Analysis.CircleDomains.Topology.JoinedPathTolls

namespace OAI

/-! Exact interior cost addition for the allowed binary join. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

def interiorPhysicalTollCost (d : PathCodeData X Y) (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞)
    (γ : FinitePhysicalPath d.domainEquiv d.basePoint) : ℝ≥0∞ :=
  (∫⁻y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint γ) +
    timeToll γ.val (Ioo (⊥ : PathTime) ⊤) m

theorem interiorPhysicalTollCost_joined (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (γ δ : FinitePhysicalPath d.domainEquiv d.basePoint) (h : γ.val ⊤ = δ.val ⊥)
    (hm : m (γ.val ⊤) = 0) :
    interiorPhysicalTollCost (X := X) (Y := Y) d g m (joinedFinitePhysicalPath d.domainEquiv hU d.basePoint γ δ h) =
      interiorPhysicalTollCost (X := X) (Y := Y) d g m γ + interiorPhysicalTollCost (X := X) (Y := Y) d g m δ := by
  unfold interiorPhysicalTollCost
  rw [physicalCost_joined d.domainEquiv hU d.basePoint γ δ h g hg]
  change _ + timeToll (joinedPath γ.val δ.val h) (Ioo (⊥ : PathTime) ⊤) m = _
  rw [joinedPath_interior_toll γ.val δ.val h m hm]
  ac_rfl


theorem exists_allowed_joined_interior_cost (d : PathCodeData X Y)
    (hU : IsOpen d.quotientDomain) (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ Δ : TaggedPhysicalPath d)
    (hΓ : AllowedTaggedPath d ν N (Γ.1.val, Γ.2))
    (hΔ : AllowedTaggedPath d ν N (Δ.1.val, Δ.2))
    (h : Γ.1.val ⊤ = Δ.1.val ⊥)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞) (hm : m (Γ.1.val ⊤) = 0)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x) :
    ∃ (ρ : FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → TagSlot),
      AllowedTaggedPath d ν N (ρ.val, θ) ∧ ρ.val ⊥ = Γ.1.val ⊥ ∧ ρ.val ⊤ = Δ.1.val ⊤ ∧
      interiorPhysicalTollCost (X := X) (Y := Y) d g m ρ =
        interiorPhysicalTollCost (X := X) (Y := Y) d g m Γ.1 + interiorPhysicalTollCost (X := X) (Y := Y) d g m Δ.1 := by
  obtain ⟨θ, hθ⟩ := exists_allowed_joined_path d hU ν N Γ Δ hΓ hΔ h hpoint
  exact ⟨joinedFinitePhysicalPath d.domainEquiv hU d.basePoint Γ.1 Δ.1 h, θ, hθ,
    joinedPath_zero _ _ h, joinedPath_one _ _ h,
    interiorPhysicalTollCost_joined d hU g hg m Γ.1 Δ.1 h hm⟩

end CircleDomainRigidity

end

end OAI
