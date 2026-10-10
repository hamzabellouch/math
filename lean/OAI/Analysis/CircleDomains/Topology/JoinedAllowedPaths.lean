import OAI.Analysis.CircleDomains.Topology.JoinedPhysicalPaths
import OAI.Analysis.CircleDomains.Modulus.InterleavedCollarCost
import OAI.Analysis.CircleDomains.Topology.AllowedPathRestriction
import OAI.Analysis.CircleDomains.Selection.AllowedCountableConcatenation

namespace OAI

/-! The binary join is allowed, with its tags constructed from one original
path and affine restrictions of the other. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSingletonClass X]
  [MeasurableSpace C(PathTime, X)]

theorem exists_allowed_joined_path
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (Γ Δ : TaggedPhysicalPath d)
    (hΓ : AllowedTaggedPath d ν N (Γ.1.val, Γ.2))
    (hΔ : AllowedTaggedPath d ν N (Δ.1.val, Δ.2))
    (h : Γ.1.val ⊤ = Δ.1.val ⊥)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x) :
    ∃θ : ℕ → TagSlot, AllowedTaggedPath d ν N (joinedPath Γ.1.val Δ.1.val h, θ) := by
  let P : ℕ → TaggedPath X := fun n => match n with
    | 0 => (Δ.1.val, Δ.2)
    | j+1 => affineRestrictedTaggedPath (collarTime (j+1)) (collarTime j) (Γ.1.val, Γ.2)
  have hP (n : ℕ) : AllowedTaggedPath d ν N (P n) := by
    cases n with
    | zero => exact hΔ
    | succ j =>
      exact allowedTaggedPath_affine d hU ν N (Γ.1.val, Γ.2) hΓ hpoint
        (collarTime_strictAnti (Nat.lt_succ_self j))
  have hfinite : physicalDomainLength d.domainEquiv d.basePoint
      (joinedPath Γ.1.val Δ.1.val h) < ∞ :=
    (joinedFinitePhysicalPath d.domainEquiv hU d.basePoint Γ.1 Δ.1 h).property
  apply exists_allowed_countable_concatenation d ν N _ hfinite
    (fun n => collarTime (n+1)) collarTime
    (fun n => collarTime_strictAnti (Nat.lt_succ_self n))
    collarCell_disjoint_interiors collarCell_complement_countable P hP
  · intro n s _
    cases n with
    | zero =>
      change joinedPath Γ.1.val Δ.1.val h
        (affinePathTime (collarTime 1) (collarTime 0) s) = Δ.1.val s
      rw [collarTime_zero]
      exact joinedPath_second Γ.1.val Δ.1.val h s
    | succ j => exact joinedPath_collar_succ Γ.1.val Δ.1.val h j s
  · exact hpoint

end CircleDomainRigidity

end

end OAI
