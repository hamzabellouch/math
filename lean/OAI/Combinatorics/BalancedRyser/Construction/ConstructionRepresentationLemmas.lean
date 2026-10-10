import OAI.Combinatorics.BalancedRyser.Construction.Construction
import OAI.Combinatorics.BalancedRyser.Hypergraph

namespace OAI

section

namespace Balanced.Configuration
open scoped _root_.Balanced

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def Represents (C : Configuration F)
    (H : PartiteHypergraph (Fintype.card F + 1) (Fintype.card F + 1)) : Prop :=
  ∃ eDir : Direction F ≃ Fin (Fintype.card F + 1),
  ∃ eLabel : ∀ d, {b // b ∈ C.labelsInDirection d} ≃ Fin (Fintype.card F + 1),
  ∃ ePoint : {p // p ∈ C.points} ≃ {e // e ∈ H.edges},
    ∀ p d b, p.val ∈ C.blockPoints b.val ↔
      (ePoint p).val (eDir d) = eLabel d b

end Balanced.Configuration

end

section

namespace Balanced
open scoped _root_.Balanced

universe u

structure ConfigurationRealization
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    (C : Configuration F)
    (H : PartiteHypergraph (Fintype.card F + 1) (Fintype.card F + 1)) where
  directionEquiv : Direction F ≃ Fin (Fintype.card F + 1)
  labelEquiv : {b : Configuration.BlockLabel F // b ∈ C.blockLabels} ≃
    PartiteHypergraph.Vertex (Fintype.card F + 1) (Fintype.card F + 1)
  edgeEquiv : {p : Point F // p ∈ C.points} ≃ {e // e ∈ H.edges}
  label_direction : ∀ b,
    (labelEquiv b).1 = directionEquiv (Configuration.blockDirection b.val)
  incidence : ∀ p b,
    p.val ∈ C.blockPoints b.val ↔
      (edgeEquiv p).val (labelEquiv b).1 = (labelEquiv b).2

def DeterministicReduction : Prop :=
  ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
    (C : Configuration F) (ρ : ℝ) (B : ℕ),
    4 ≤ Fintype.card F → 0 < ρ → ρ < 1 →
    C.Valid → C.Compatible → C.Occupancy ρ B →
    C.CoreConcentration ρ → C.LocalCondition →
    2 * (1 + (B : ℝ)) < ρ * Fintype.card F →
    ∃ H : PartiteHypergraph (Fintype.card F + 1) (Fintype.card F + 1),
      H.Intersecting ∧ H.Nonisolated ∧ H.HasCoverNumber (Fintype.card F + 1) ∧
      Nonempty (ConfigurationRealization C H)

end Balanced

end

end OAI
