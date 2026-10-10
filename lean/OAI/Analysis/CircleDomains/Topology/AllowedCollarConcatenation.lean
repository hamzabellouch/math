import OAI.Analysis.CircleDomains.Modulus.CountablePhysicalLength
import OAI.Analysis.CircleDomains.Selection.AllowedCountableConcatenation

namespace OAI

/-! The constructed countable collar path is allowed when its actual
physical lengths are summable. No path-stability input is assumed. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace C(PathTime, X)]

def collarTaggedPath (p : X) (Γ : ℕ → TaggedPath X)
    (hjoin : ∀ n, (Γ (n + 1)).1 ⊤ = (Γ n).1 ⊥)
    (htail : ∀ V ∈ 𝓝 p, ∃ N : ℕ, ∀ n ≥ N, ∀ s, (Γ n).1 s ∈ V) : TaggedPath X :=
  concatenatedTaggedPath (collarConcatenation p (fun n => (Γ n).1) hjoin htail)
    (fun n => collarTime (n + 1)) collarTime Γ

theorem allowedTaggedPath_collar (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (p : X) (Γ : ℕ → TaggedPath X)
    (hjoin : ∀ n, (Γ (n + 1)).1 ⊤ = (Γ n).1 ⊥)
    (htail : ∀ V ∈ 𝓝 p, ∃ k : ℕ, ∀ n ≥ k, ∀ s, (Γ n).1 s ∈ V)
    (hΓ : ∀ n, AllowedTaggedPath d ν N (Γ n))
    (hfinite : (∑' n, physicalDomainLength d.domainEquiv d.basePoint (Γ n).1) < ∞)
    (hpoint : ∀ i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x) :
    AllowedTaggedPath d ν N (collarTaggedPath p Γ hjoin htail) := by
  let γ : ℕ → FinitePhysicalPath d.domainEquiv d.basePoint := fun n => ⟨(Γ n).1, (hΓ n).1⟩
  apply allowedTaggedPath_concatenated d ν N
    (collarConcatenation p (fun n => (Γ n).1) hjoin htail)
    ((physicalDomainLength_collarPieces_le d.domainEquiv hU d.basePoint γ _
      (collarConcatenation_affine p (fun n => (Γ n).1) hjoin htail)).trans_lt hfinite)
    (fun n => collarTime (n + 1)) collarTime
    (fun n => collarTime_strictAnti (Nat.lt_succ_self n))
    collarCell_disjoint_interiors collarCell_complement_countable Γ hΓ
  · intro n s _
    exact collarConcatenation_affine p (fun n => (Γ n).1) hjoin htail n s
  · exact hpoint

end CircleDomainRigidity

end

end OAI
