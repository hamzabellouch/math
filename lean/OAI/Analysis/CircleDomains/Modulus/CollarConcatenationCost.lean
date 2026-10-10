import OAI.Analysis.CircleDomains.Topology.AllowedCollarConcatenation
import OAI.Analysis.CircleDomains.Selection.CountableConcatenationTolls
import OAI.Analysis.CircleDomains.Modulus.PositivePhysicalCost

namespace OAI

/-! The actual allowed collar concatenation with its complete cost identity.
Summable cost and a positive density supply the required physical finiteness. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem exists_allowed_collar_of_summable_cost
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain) (hG : IsOpen d.physicalDomain)
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀ n : ℕ, (Fin (n + 1) → ℕ) → Set (Fin (n + 1) → UnitAddCircle))
    (p : X) (γ : ℕ → FinitePhysicalPath d.domainEquiv d.basePoint) (θ : ℕ → ℕ → TagSlot)
    (hΓ : ∀ n, AllowedTaggedPath d ν N ((γ n).val, θ n))
    (hjoin : ∀ n, (γ (n + 1)).val ⊤ = (γ n).val ⊥)
    (htail : ∀ V ∈ 𝓝 p, ∃ k : ℕ, ∀ n ≥ k, ∀ s, (γ n).val s ∈ V)
    (g : Y → ℝ≥0∞) (hg : Measurable g) (m : X → ℝ≥0∞)
    (c : ℝ≥0∞) (hc : c ≠ 0) (hpos : ∀ y ∈ d.physicalDomain, c ≤ g y)
    (hzero : ∀ n, m ((γ n).val ⊥) = 0) (hone : ∀ n, m ((γ n).val ⊤) = 0)
    (hcost : (∑' n, ((∫⁻ y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint (γ n)) +
      boundaryToll (γ n).val m)) < ∞)
    (hpoint : ∀ i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x) :
    ∃ (η : FinitePhysicalPath d.domainEquiv d.basePoint) (tags : ℕ → TagSlot),
      AllowedTaggedPath d ν N (η.val, tags) ∧ η.val ⊥ = p ∧ η.val ⊤ = (γ 0).val ⊤ ∧
      (∫⁻ y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint η) +
        timeToll η.val (Ioo (⊥ : PathTime) ⊤) m =
      ∑' n, ((∫⁻ y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint (γ n)) +
        boundaryToll (γ n).val m) := by
  have hphys : (∑' n, ∫⁻ y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint (γ n)) < ∞ :=
    (ENNReal.tsum_le_tsum (fun n => show
      (∫⁻ y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint (γ n)) ≤
        (∫⁻ y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint (γ n)) +
          boundaryToll (γ n).val m from le_self_add)).trans_lt hcost
  have hlen := sum_physicalLength_finite_of_cost d.domainEquiv hG d.basePoint γ g c hc hpos hphys
  let η := finitePhysicalCollarConcatenation d.domainEquiv hU d.basePoint p γ hjoin htail hlen
  let Γ : ℕ → TaggedPath X := fun n => ((γ n).val, θ n)
  refine ⟨η, (collarTaggedPath p Γ hjoin htail).2, ?_, ?_, ?_, ?_⟩
  · exact allowedTaggedPath_collar d hU ν N p Γ hjoin htail hΓ hlen hpoint
  · exact collarConcatenation_zero p (fun n => (γ n).val) hjoin htail
  · exact collarConcatenation_one p (fun n => (γ n).val) hjoin htail
  · have hmatch : ∀ n s, η.val (affinePathTime (collarTime (n + 1)) (collarTime n) s) =
        (γ n).val s := collarConcatenation_affine p (fun n => (γ n).val) hjoin htail
    rw [physicalCost_collarPieces d.domainEquiv hU d.basePoint η γ hmatch g hg]
    change (∑' n, ∫⁻ y, g y ∂dyadicPhysicalOccupation d.domainEquiv d.basePoint (γ n)) +
      timeToll (collarConcatenation p (fun n => (γ n).val) hjoin htail) (Ioo ⊥ ⊤) m = _
    rw [collarConcatenation_interior_toll p (fun n => (γ n).val) hjoin htail m hzero hone,
      ENNReal.tsum_add]

end CircleDomainRigidity

end

end OAI
