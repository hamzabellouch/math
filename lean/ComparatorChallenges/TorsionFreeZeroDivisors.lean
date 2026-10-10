import Mathlib

namespace OAI

namespace TorsionFreeZeroDivisors

/-- Ordinary group torsion-freeness, without requiring uniqueness of all roots. -/
def TorsionFree (G : Type) [Group G] : Prop :=
  ∀ (g : G) (n : ℕ), 0 < n → g ^ n = 1 → g = 1

/-- A connected finite Hausdorff 2-dimensional CW K(G,1). -/
def HasFiniteTwoDimensionalClassifyingSpace (G : Type) [Group G] : Prop :=
  ∃ (X : Type) (topX : TopologicalSpace X),
    letI : TopologicalSpace X := topX
    ∃ (_hausdorff : T2Space X) (_connected : PathConnectedSpace X)
      (cw : Topology.CWComplex (Set.univ : Set X)),
      letI : Topology.CWComplex (Set.univ : Set X) := cw
      Topology.CWComplex.Finite (Set.univ : Set X) ∧
      (∀ n : ℕ, 2 < n → IsEmpty (Topology.CWComplex.cell (Set.univ : Set X) n)) ∧
      Nonempty (Topology.CWComplex.cell (Set.univ : Set X) 2) ∧
      ∃ (x : X), Nonempty (G ≃* FundamentalGroup X x) ∧
        ∃ (E : Type) (topE : TopologicalSpace E),
          letI : TopologicalSpace E := topE
          ContractibleSpace E ∧
          ∃ p : E → X, IsCoveringMap p ∧ Function.Surjective p

/-- The entire main theorem, including its "Moreover" clause. -/
def MainTheorem : Prop :=
  ∃ (G : Type) (inst : Group G),
    letI : Group G := inst
    Group.IsFinitelyPresented G ∧ TorsionFree G ∧
    HasFiniteTwoDimensionalClassifyingSpace G ∧
    ∃ α β : MonoidAlgebra (ZMod 2) G, α ≠ 0 ∧ β ≠ 0 ∧ α * β = 0

theorem main : MainTheorem := by
  sorry

end TorsionFreeZeroDivisors

end OAI
