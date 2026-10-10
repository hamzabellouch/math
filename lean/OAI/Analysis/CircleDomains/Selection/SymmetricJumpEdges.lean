import OAI.Analysis.CircleDomains.Selection.FiniteJumpSystems
import OAI.Analysis.CircleDomains.Probability.ReversedPhysicalOccupation
import OAI.Analysis.CircleDomains.Topology.AllowedPathReversal

namespace OAI

/-! True path reversal and symmetric jumps make every installed chain
relation symmetric, with exactly the same costs. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y I : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem physicalJumpEdge_symmetric
    (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) (V : I → Set X) (T : I → ℝ≥0∞)
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    {x y : X} {a : ℝ≥0∞} (h : physicalJumpEdge d ν N g m V T x y a) :
    physicalJumpEdge d ν N g m V T y x a := by
  rcases h with ⟨Γ, hΓ, hΓ0, hΓ1, hxU, hyU, hcost⟩ | ⟨i, hx, hy, ha⟩
  · refine Or.inl ⟨reversedTaggedPhysicalPath d Γ, ?_, ?_, ?_, hyU, hxU, ?_⟩
    · exact allowedTaggedPath_reversed d ν N (Γ.1.val, Γ.2) hΓ hpoint
    · change Γ.1.val (unitInterval.symm 0) = y
      rw [unitInterval.symm_zero]
      exact hΓ1
    · change Γ.1.val (unitInterval.symm 1) = x
      rw [unitInterval.symm_one]
      exact hΓ0
    · exact (physicalTollCost_reversed d g m Γ.1).trans hcost
  · exact Or.inr ⟨i, hy, hx, ha⟩

end CircleDomainRigidity

end

end OAI
