import OAI.Analysis.CircleDomains.Selection.PaidBlockAssembly
import OAI.Analysis.CircleDomains.Uniformization.FiniteLimitBlock

namespace OAI

/-! The concrete edges in a chain with fixed old jump disks. True edges
are actual allowed physical paths, and jump edges keep their original toll. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y I : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

def physicalJumpEdge (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) (V : I → Set X) (c : I → ℝ≥0∞)
    (x y : X) (a : ℝ≥0∞) : Prop :=
  (∃Γ : TaggedPhysicalPath d, AllowedTaggedPath d ν N (Γ.1.val, Γ.2) ∧
    Γ.1.val ⊥ = x ∧ Γ.1.val ⊤ = y ∧ x ∈ d.quotientDomain ∧ y ∈ d.quotientDomain ∧
    physicalTollCost d g m Γ.1 = a) ∨
  (∃i, x ∈ V i ∩ d.quotientDomain ∧ y ∈ V i ∩ d.quotientDomain ∧ a = c i)

theorem physicalJumpEdge_of_path (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) (V : I → Set X) (c : I → ℝ≥0∞)
    (Γ : TaggedPhysicalPath d) (hΓ : AllowedTaggedPath d ν N (Γ.1.val, Γ.2))
    (hx : Γ.1.val ⊥ ∈ d.quotientDomain) (hy : Γ.1.val ⊤ ∈ d.quotientDomain) :
    physicalJumpEdge d ν N g m V c (Γ.1.val ⊥) (Γ.1.val ⊤) (physicalTollCost d g m Γ.1) :=
  Or.inl ⟨Γ, hΓ, rfl, rfl, hx, hy, rfl⟩

theorem physicalJumpEdge_of_jump (d : PathCodeData X Y) (ν : Measure X)
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) (V : I → Set X) (c : I → ℝ≥0∞)
    (i : I) {x y : X} (hx : x ∈ V i ∩ d.quotientDomain) (hy : y ∈ V i ∩ d.quotientDomain) :
    physicalJumpEdge d ν N g m V c x y (c i) := Or.inr ⟨i, hx, hy, rfl⟩

end CircleDomainRigidity

end

end OAI
